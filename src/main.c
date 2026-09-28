/*
  * Copyright (c) 2022 Nordic Semiconductor ASA
  * SPDX-License-Identifier: LicenseRef-Nordic-5-Clause
  * 
  * Copyright (c) 2023 LooUQ, Inc.
  * SPDX-License-Identifier: Apache-2.0
 */

#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>

#include <zephyr/drivers/gpio.h>
#include <zephyr/shell/shell.h>

#include <date_time.h>
#include <modem/lte_lc.h>
#include <modem/nrf_modem_lib.h>
#include <modem/ntn.h>
#include <nrf_modem_at.h>
#include <nrf_modem_gnss.h>

K_SEM_DEFINE(lte_connected, 0, 1);

/* Given to the main thread when the GNSS receiver produces a valid fix. */
K_SEM_DEFINE(gnss_fix_sem, 0, 1);

/* Device position supplied to the modem for NTN Doppler/timing pre-compensation.
 * In fixed mode it comes from CONFIG_NTN_LOCATION; in dynamic mode from the
 * internal GNSS receiver.
 */
static double loc_lat;
static double loc_lon;
static float  loc_alt;

/* true  = CONFIG_NTN_LOCATION supplied a valid fixed position (GNSS skipped);
 * false = position is acquired from internal GNSS. Set once at startup.
 */
static bool location_is_fixed;

/* Set by ntn_handler() when the modem needs a fresh location and the cached fix
 * is too old to reuse. Handled by the main loop (dynamic mode only).
 */
static volatile bool refix_requested;

/* Uptime (ms) of the last GNSS fix, for the NTN_REFIX_MIN_INTERVAL_S guard. */
static int64_t last_fix_uptime;

/* Time-to-first-fix (s) of the most recent GNSS acquisition, for the shell. */
static int last_ttff_s;

/* Coarse app phase, reported by "gnss status" / "udp status". */
enum app_phase {
	PHASE_INIT,
	PHASE_GNSS_FIX,
	PHASE_ATTACHING,
	PHASE_CONNECTED,
	PHASE_NO_SERVICE,
};
static enum app_phase app_phase;

static const char *phase_str(enum app_phase p)
{
	switch (p) {
	case PHASE_GNSS_FIX:	return "acquiring GNSS fix";
	case PHASE_ATTACHING:	return "attaching";
	case PHASE_CONNECTED:	return "connected";
	case PHASE_NO_SERVICE:	return "no service (both networks grounded)";
	default:		return "init";
	}
}

/* Latest GNSS PVT frame, filled by gnss_event_handler() in modem callback
 * context and read by the main thread once gnss_fix_sem is given.
 */
static struct nrf_modem_gnss_pvt_data_frame gnss_pvt;

/* UDP socket, kept open after the initial send so messages can be sent
 * manually with the "udp send <text>" shell command. -1 until registered.
 */
static int udp_fd = -1;

/* Running field-test tallies. cycles counts periodic loop iterations; good
 * sends/receives count successful send()/recv() calls (including manual
 * "udp send", which also flows through udp_send_and_recv()).
 */
static unsigned int total_cycles;
static unsigned int good_sends;
static unsigned int good_recvs;

/* log_tally() reads the time, but read_unix_time() is defined later with the
 * other modem helpers. */
static int64_t read_unix_time(void);

/* Network service control inputs, from the zephyr,user node in the board
 * overlay (P0.21 cellular, P0.22 satellite). Active-low with the internal
 * pull-up: a floating pin leaves the network available, a pin grounded forces
 * it out of service. A property missing from the devicetree leaves that network
 * always available. Polled, not interrupt-driven.
 *
 * Cellular has priority: with both pins floating the device uses cellular.
 */
enum svc_net {
	SVC_TN,		/* terrestrial cellular */
	SVC_NTN,	/* satellite */
	SVC_COUNT,
	SVC_NONE = SVC_COUNT,
};

#define ZEPHYR_USER DT_PATH(zephyr_user)

static const struct gpio_dt_spec svc_disable_pin[SVC_COUNT] = {
	[SVC_TN]  = GPIO_DT_SPEC_GET_OR(ZEPHYR_USER, tn_disable_gpios, {0}),
	[SVC_NTN] = GPIO_DT_SPEC_GET_OR(ZEPHYR_USER, ntn_disable_gpios, {0}),
};
static const char *const svc_name[SVC_COUNT + 1] = { "Cellular", "Satellite", "none" };
static bool svc_pin_ready[SVC_COUNT];
static bool svc_was_disabled[SVC_COUNT];

/* true if the control pin currently forces this network out of service. Logs
 * each change, so a capture shows which outages were forced by the pin.
 */
static bool svc_disabled(enum svc_net net)
{
	bool disabled = svc_pin_ready[net] &&
			gpio_pin_get_dt(&svc_disable_pin[net]) == 1;

	if (disabled != svc_was_disabled[net]) {
		printk("%s control pin %s: network %s\n", svc_name[net],
		       disabled ? "GROUNDED" : "released",
		       disabled ? "OUT OF SERVICE" : "available");
		svc_was_disabled[net] = disabled;
	}
	return disabled;
}

/* Configure the control pins as pulled-up inputs and log their initial state. */
static void svc_pins_init(void)
{
	for (int i = 0; i < SVC_COUNT; i++) {
		const struct gpio_dt_spec *pin = &svc_disable_pin[i];

		if (!pin->port) {
			continue;
		}
		if (!gpio_is_ready_dt(pin) ||
		    gpio_pin_configure_dt(pin, GPIO_INPUT) != 0) {
			printk("%s control pin unavailable\n", svc_name[i]);
			continue;
		}
		svc_pin_ready[i] = true;
		printk("%s control pin %u configured\n", svc_name[i], pin->pin);
		(void)svc_disabled(i);
	}
}

/* Network the modem is currently attached to (SVC_NONE while detached). */
static enum svc_net link_net = SVC_NONE;

/* Set when a cellular attach fails and the device falls back to satellite.
 * Cellular is retried CONFIG_LINK_TN_PROBE_INTERVAL_S after tn_fail_uptime.
 */
static bool tn_fallback;
static int64_t tn_fail_uptime;

/* Pick the network to use from the control pins. Cellular wins when its pin
 * floats, unless it just failed to attach and satellite is available, in which
 * case satellite is used until the retry interval elapses.
 */
static enum svc_net link_choose(void)
{
	bool tn_ok = !svc_disabled(SVC_TN);
	bool ntn_ok = !svc_disabled(SVC_NTN);

	if (!tn_ok) {
		/* Releasing the pin again retries cellular straight away. */
		tn_fallback = false;
	}

	if (tn_ok && tn_fallback && ntn_ok &&
	    (k_uptime_get() - tn_fail_uptime) <
		    (int64_t)CONFIG_LINK_TN_PROBE_INTERVAL_S * 1000) {
		return SVC_NTN;
	}
	if (tn_ok) {
		return SVC_TN;
	}
	if (ntn_ok) {
		return SVC_NTN;
	}
	return SVC_NONE;
}

/* Advance past any characters that cannot start a number (quotes, commas,
 * spaces), so the CONFIG_NTN_LOCATION string can be tokenized with strtod
 * regardless of whether the values are quoted.
 */
static const char *skip_to_number(const char *p)
{
	while (*p && *p != '+' && *p != '-' && *p != '.' &&
	       (*p < '0' || *p > '9')) {
		p++;
	}
	return p;
}

/* Parse "lat,lon,alt" (as configured in CONFIG_NTN_LOCATION) into numeric
 * values for ntn_location_set(). Returns 0 on success, -1 on parse error.
 */
static int parse_location(const char *str, double *lat, double *lon, float *alt)
{
	char *end;
	const char *p = skip_to_number(str);

	*lat = strtod(p, &end);
	if (end == p) {
		return -1;
	}

	p = skip_to_number(end);
	*lon = strtod(p, &end);
	if (end == p) {
		return -1;
	}

	p = skip_to_number(end);
	*alt = (float)strtod(p, &end);
	if (end == p) {
		return -1;
	}

	return 0;
}

static void ntn_handler(const struct ntn_evt *evt)
{
	int err;

	switch (evt->type) {
	case NTN_EVT_LOCATION_REQUEST:
		if (!evt->location_request.requested) {
			break;
		}

		printk("NTN location requested (accuracy %u m)\n",
		       evt->location_request.accuracy);

		/* NTN requires the modem to know the device position for
		 * Doppler/timing pre-compensation. In fixed mode the position never
		 * changes, so answer immediately from the cached coordinates. In
		 * dynamic mode, reuse the cached GNSS fix if it is recent enough;
		 * otherwise ask the main loop to drop NTN and acquire a fresh fix
		 * (internal GNSS cannot run while NTN is active).
		 */
		if (location_is_fixed ||
		    (k_uptime_get() - last_fix_uptime) <
			    (int64_t)CONFIG_NTN_REFIX_MIN_INTERVAL_S * 1000) {
			err = ntn_location_set(loc_lat, loc_lon, loc_alt,
					       CONFIG_NTN_LOCATION_VALIDITY_S);
			if (err) {
				printk("ntn_location_set failed, error: %d\n", err);
			}
		} else {
			refix_requested = true;
		}
		break;
	default:
		printk("Unknown NTN event: %d\n", evt->type);
		break;
	}
}

static void lte_handler(const struct lte_lc_evt *const evt)
{
	switch (evt->type) {
	case LTE_LC_EVT_NW_REG_STATUS:
		if ((evt->nw_reg_status != LTE_LC_NW_REG_REGISTERED_HOME) &&
		    (evt->nw_reg_status != LTE_LC_NW_REG_REGISTERED_ROAMING)) {
			/* Satellite registration can take minutes and pass through
			 * several intermediate states. Distinguish the transient
			 * "still searching" states from the ones the network rejects
			 * us with, so a stuck attach is obvious instead of looking
			 * like it is merely slow.
			 */
			const char *reason;

			switch (evt->nw_reg_status) {
			case LTE_LC_NW_REG_SEARCHING:
				reason = "searching";
				break;
			case LTE_LC_NW_REG_REGISTRATION_DENIED:
				reason = "DENIED by network";
				break;
			case LTE_LC_NW_REG_NO_SUITABLE_CELL:
				reason = "no suitable cell (PLMN/cell rejected)";
				break;
			case LTE_LC_NW_REG_UICC_FAIL:
				reason = "UICC/SIM failure";
				break;
			default:
				reason = "not registered";
				break;
			}
			printk("Network registration status: %d (%s)\n",
			       evt->nw_reg_status, reason);
			break;
		}

		printk("Network registration status: %s\n",
		       evt->nw_reg_status == LTE_LC_NW_REG_REGISTERED_HOME ?
		       "Connected - home network" : "Connected - roaming");
		k_sem_give(&lte_connected);
		break;
	case LTE_LC_EVT_RRC_UPDATE:
		printk("RRC mode: %s\n",
		       evt->rrc_mode == LTE_LC_RRC_MODE_CONNECTED ?
		       "Connected" : "Idle");
		break;
	case LTE_LC_EVT_CELL_UPDATE:
		printk("LTE cell changed: Cell ID: %d, Tracking area: %d\n",
		       evt->cell.id, evt->cell.tac);
		break;
	case LTE_LC_EVT_MODEM_EVENT:
		printk("Modem event: %d\n", evt->modem_evt.type);
		break;
	default:
		break;
	}
}

/* Accuracy (m) reported with the proactive location. Match this to the
 * AT%LOCATION=2 command that registers for you manually. The validity comes
 * from CONFIG_NTN_LOCATION_VALIDITY_S (0 = infinite, for a stationary device).
 */
#define NTN_LOCATION_ACCURACY_M	100

/* Push the device position to the modem (AT%LOCATION=2). Done before connecting
 * so satellite acquisition can start (otherwise NTN registration searches
 * endlessly); ntn_handler() keeps it refreshed for later modem requests.
 * Returns 0 on success, -1 on error.
 */
static int set_modem_location(double lat, double lon, float alt, int validity)
{
	int err = nrf_modem_at_printf(
		"AT%%LOCATION=2,\"%.6f\",\"%.6f\",\"%.1f\",%d,%d",
		lat, lon, (double)alt, NTN_LOCATION_ACCURACY_M, validity);

	if (err) {
		printk("Set location failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}
	printk("NTN location set: lat %.6f, lon %.6f, alt %.1f m, validity %d s\n",
	       lat, lon, (double)alt, validity);
	return 0;
}

/* Called in modem library context for each GNSS event. On a valid PVT fix,
 * cache the frame and wake the acquiring thread. Keep it short.
 */
static void gnss_event_handler(int event)
{
	if (event != NRF_MODEM_GNSS_EVT_PVT) {
		return;
	}

	if (nrf_modem_gnss_read(&gnss_pvt, sizeof(gnss_pvt),
				NRF_MODEM_GNSS_DATA_PVT) == 0 &&
	    (gnss_pvt.flags & NRF_MODEM_GNSS_PVT_FLAG_FIX_VALID)) {
		k_sem_give(&gnss_fix_sem);
	}
}

/* Acquire a position from the internal GNSS receiver into loc_lat/lon/alt.
 * Internal GNSS and NTN are mutually exclusive system modes, so this drops the
 * modem to CFUN=0, switches to GNSS-only, runs a single fix, then returns the
 * modem to CFUN=0 for the caller to re-attach to NTN. Blocks until a valid fix
 * (CONFIG_GNSS_FIX_RETRY_S = 0) or restarts the receiver on each retry timeout.
 * Returns 0 on success, -1 on setup error.
 */
static int acquire_gnss_location(void)
{
	int64_t start;
	int err;

	printk("Acquiring GNSS fix...\n");
	app_phase = PHASE_GNSS_FIX;

	(void)nrf_modem_at_printf("AT+CFUN=0");

	err = nrf_modem_at_printf("AT%%XSYSTEMMODE=0,0,1,0");
	if (err) {
		printk("Set GNSS system mode failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}

	if (nrf_modem_gnss_event_handler_set(gnss_event_handler) != 0 ||
	    nrf_modem_gnss_fix_interval_set(0) != 0 ||	/* single fix */
	    nrf_modem_gnss_fix_retry_set(CONFIG_GNSS_FIX_RETRY_S) != 0) {
		printk("GNSS configuration failed\n");
		return -1;
	}

	/* Activate GNSS only (CFUN=31 leaves LTE untouched; it is already off). */
	err = nrf_modem_at_printf("AT+CFUN=31");
	if (err) {
		printk("Activate GNSS failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}

	start = k_uptime_get();
	for (;;) {
		if (nrf_modem_gnss_start() != 0) {
			printk("GNSS start failed\n");
			return -1;
		}

		/* With fix_retry 0 GNSS runs until a valid fix, so K_FOREVER
		 * pairs exactly; with a timeout, restart the receiver and retry.
		 */
		if (k_sem_take(&gnss_fix_sem,
			       CONFIG_GNSS_FIX_RETRY_S == 0 ? K_FOREVER :
			       K_SECONDS(CONFIG_GNSS_FIX_RETRY_S + 30)) == 0) {
			break;
		}

		printk("GNSS: no fix yet, retrying\n");
		(void)nrf_modem_gnss_stop();
	}

	loc_lat = gnss_pvt.latitude;
	loc_lon = gnss_pvt.longitude;
	loc_alt = gnss_pvt.altitude;
	last_fix_uptime = k_uptime_get();
	last_ttff_s = (int)((last_fix_uptime - start) / 1000);

	printk("GNSS fix: lat %.6f, lon %.6f, alt %.1f m (TTFF %d s)\n",
	       loc_lat, loc_lon, (double)loc_alt, last_ttff_s);

	(void)nrf_modem_gnss_stop();
	(void)nrf_modem_at_printf("AT+CFUN=0");

	return 0;
}

static void modem_init(void)
{
	int err;

	err = nrf_modem_lib_init();
	if (err) {
		printk("Modem library initialization failed, error: %d\n", err);
		return;
	}

	(void)nrf_modem_at_printf("AT+CMEE=1");

	/* Configure the COEX0 pin that gates the external GNSS LNA/RF path before
	 * any RF activity. The modem stores this and toggles COEX0 automatically
	 * per RF frequency thereafter. Board-specific; empty string skips it.
	 */
	if (strlen(CONFIG_GNSS_COEX0_CMD) > 0) {
		err = nrf_modem_at_printf("%s", CONFIG_GNSS_COEX0_CMD);
		if (err) {
			printk("COEX0 config failed, type: %d, error: %d\n",
			       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		} else {
			printk("COEX0 GNSS path configured: %s\n",
			       CONFIG_GNSS_COEX0_CMD);
		}
	}

	/* Register for modem location requests required for NTN operation. */
	ntn_register_handler(ntn_handler);
}

static void modem_connect(void)
{
	int err = lte_lc_connect_async(lte_handler);

	if (err) {
		printk("Connecting to LTE network failed, error: %d\n", err);
		return;
	}
}

static int udp_pdn_setup(void)
{
	int cid = 0;
	int err;

	if (IS_ENABLED(CONFIG_UDP_ALLOC_NEW_CID)) {
		err = nrf_modem_at_scanf("AT%XNEWCID?", "%%XNEWCID: %d", &cid);
		if (err == 1) {
			printf("Created CID %d\n", cid);
		} else {
			printf("Create CID failed, error: %d\n", err);
			return -1;
		}
	}

	err = nrf_modem_at_printf("AT+CGDCONT=%d,\"IP\",\"%s\"", cid, CONFIG_UDP_APN);
	if (err == 0) {
		printk("Configured IPv4 for APN \"%s\"\n", CONFIG_UDP_APN);
	} else {
		printf("Configure PDN failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}

	return cid;
}

static int udp_pdn_activate(int cid)
{
	char xgetpdnid[18];
	int pdn_id;
	int err;

	if (IS_ENABLED(CONFIG_UDP_ALLOC_NEW_CID)) {
		err = nrf_modem_at_printf("AT+CGACT=1,%d", cid);
		if (err == 0) {
			printk("Activated CID %d\n", cid);
		} else {
			printk("Activate CID failed, type: %d, error: %d\n",
			       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
			return -1;
		}
	}

	(void)snprintf(xgetpdnid, sizeof(xgetpdnid), "AT%%XGETPDNID=%u", cid);
	err = nrf_modem_at_scanf(xgetpdnid, "%%XGETPDNID: %d", &pdn_id);
	if (err == 1) {
		printk("Get PDN ID %d\n", pdn_id);
	} else {
		printk("Get PDN ID failed, error: %d\n", err);
		return -1;
	}

	return pdn_id;
}

static void udp_socket_close(int fd)
{
	int err;

	err = close(fd);
	if (err == 0) {
		printk("Closed socket %d\n", fd);
	} else {
		printk("Close socket failed, error: %d, errno: %d\n", err, errno);
	}
}

static int udp_socket_setup(int pdn_id)
{
	struct addrinfo hints = {
		.ai_family = AF_INET,
		.ai_socktype = SOCK_DGRAM,
	};
	struct addrinfo *res;
	struct timeval recv_timeout = {
		.tv_sec = CONFIG_UDP_RECV_TIMEOUT_S
	};
	int fd, err;

	err = getaddrinfo(CONFIG_UDP_SERVER_ADDRESS, NULL, &hints, &res);
	if (err) {
		printk("getaddrinfo failed for \"%s\", error: %d\n",
		       CONFIG_UDP_SERVER_ADDRESS, err);
		return -1;
	}
	((struct sockaddr_in *)res->ai_addr)->sin_port = htons(CONFIG_UDP_SERVER_PORT);

	fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
	if (fd < 0) {
		printk("Create socket failed, error: %d, errno: %d\n", fd, errno);
		freeaddrinfo(res);
		return -1;
	}
	printk("Created socket %d\n", fd);

	if (IS_ENABLED(CONFIG_UDP_ALLOC_NEW_CID)) {
		err = setsockopt(fd, SOL_SOCKET, SO_BINDTOPDN, &pdn_id, sizeof(pdn_id));
		if (err == 0) {
			printk("Bound to PDN ID %d\n", pdn_id);
		} else {
			printk("Bind to PDN failed, error: %d, errno: %d\n", err, errno);
			goto error_close_socket;
		}
	}

	err = setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &recv_timeout, sizeof(recv_timeout));
	if (err != 0) {
		printk("Set receive timeout failed, error: %d, errno: %d\n", err, errno);
		goto error_close_socket;
	}

	/* Fix the peer so send()/recv() can be used (keeping the shell command
	 * simple). For UDP, connect() only records the default destination; it
	 * does not put any packet on the air.
	 */
	err = connect(fd, res->ai_addr, res->ai_addrlen);
	if (err != 0) {
		printk("Connect failed, error: %d, errno: %d\n", err, errno);
		goto error_close_socket;
	}
	printk("UDP socket targeting %s:%d\n", CONFIG_UDP_SERVER_ADDRESS,
	       CONFIG_UDP_SERVER_PORT);

	freeaddrinfo(res);
	return fd;

error_close_socket:
	freeaddrinfo(res);
	udp_socket_close(fd);

	return -1;
}

static void udp_send_and_recv(int fd, const void *payload, size_t payload_len)
{
	char buffer[256];
	ssize_t len;

	len = send(fd, payload, payload_len, 0);
	if (len == (ssize_t)payload_len) {
		good_sends++;
		printk("Sent %d bytes: %.*s\n", len, (int)payload_len,
		       (const char *)payload);
	} else {
		printk("Send failed, error: %d, errno: %d\n", len, errno);
		return;
	}

	/* Give the reply time to arrive before listening for it. On high-latency
	 * NTN links the response is not back immediately, so a short gap between
	 * send and receive avoids burning the recv timeout on an empty socket.
	 */
	if (CONFIG_UDP_RECV_DELAY_MS > 0) {
		k_sleep(K_MSEC(CONFIG_UDP_RECV_DELAY_MS));
	}

	len = recv(fd, buffer, sizeof(buffer) - 1, 0);
	if (len > 0) {
		good_recvs++;
		buffer[len] = '\0';
		printk("Received %d bytes: %s\n", len, buffer);
	} else if (len < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
		/* recv timed out (SO_RCVTIMEO) with no reply - normal for UDP over
		 * a high-latency satellite link, not a failure.
		 */
		printk("** No reply within recv timeout: %ds\n", CONFIG_UDP_RECV_TIMEOUT_S);
	} else if (len < 0) {
		printk("Receive failed, error: %d, errno: %d\n", len, errno);
	}
}

/* Print the running send/receive tallies, prefixed with the current time as
 * UTC (converted from the date_time epoch). Shows "unknown" until time is
 * acquired.
 */
static void log_tally(void)
{
	int64_t epoch = read_unix_time();
	char when[32] = "unknown";

	if (epoch > 0) {
		time_t t = (time_t)epoch;
		struct tm tm;

		gmtime_r(&t, &tm);
		strftime(when, sizeof(when), "%Y-%m-%d %H:%M:%S UTC", &tm);
	}

	printk("Tally: time=%s cycles=%u good_sends=%u good_recvs=%u\n",
	       when, total_cycles, good_sends, good_recvs);
}

/* Read the satellite link quality once registered. %CONEVAL is rejected in
 * NTN mode (+CME ERROR 534), so use the standard +CESQ instead and decode the
 * NB-IoT fields: RSRP dBm = <rsrp> - 140, RSRQ dB = <rsrq>/2 - 19.5. A value of
 * 255 means the level is not known or not detectable.
 *
 * Returns 0 and fills *rsrp_dbm / *rsrq_db on success, 1 if the level is not
 * detectable, or -1 on query error.
 */
static int read_signal_quality(int *rsrp_dbm, double *rsrq_db)
{
	int rsrq, rsrp;
	int err;

	err = nrf_modem_at_scanf("AT+CESQ",
				 "+CESQ: %*d,%*d,%*d,%*d,%d,%d", &rsrq, &rsrp);
	if (err != 2) {
		return -1;
	}

	if (rsrp == 255) {
		return 1;
	}

	*rsrp_dbm = rsrp - 140;
	*rsrq_db = (rsrq == 255) ? 0.0 : (rsrq / 2.0) - 19.5;
	return 0;
}

/* Read the <snr> field from %XMONITOR and decode it to dB. %CONEVAL (the usual
 * SNR source) is rejected in NTN mode, but %XMONITOR carries it:
 *   <reg_status>,<full_name>,<short_name>,<plmn>,<tac>,<AcT>,<band>,<cell_id>,
 *   <phys_cell_id>,<EARFCN>,<rsrp>,<snr>,...
 * SNR is reported as an index: dB = value - 24; 127 = not known/not detectable.
 * Returns 0 and fills *snr_db on success, 1 if SNR is unavailable, -1 on error.
 */
#define XMONITOR_SNR_FIELD 11

static int read_snr(int *snr_db)
{
	char resp[160];
	const char *p;
	int field = 0;
	bool in_quote = false;
	int snr_index;

	if (nrf_modem_at_cmd(resp, sizeof(resp), "AT%%XMONITOR")) {
		return -1;
	}

	p = strchr(resp, ' '); /* skip past "%XMONITOR:" */
	if (p == NULL) {
		return -1;
	}
	p++;

	/* Advance to the start of the SNR field, ignoring commas inside the quoted
	 * operator-name/PLMN/TAC/cell-id fields.
	 */
	while (*p != '\0' && field < XMONITOR_SNR_FIELD) {
		if (*p == '"') {
			in_quote = !in_quote;
		} else if (*p == ',' && !in_quote) {
			field++;
		}
		p++;
	}
	if (field != XMONITOR_SNR_FIELD || *p == '\0' || *p == ',') {
		return 1; /* not registered yet / field empty */
	}

	snr_index = atoi(p);
	if (snr_index == 127) {
		return 1; /* not known or not detectable */
	}

	*snr_db = snr_index - 24;
	return 0;
}

static void log_signal_quality(void)
{
	int rsrp;
	double rsrq;
	int snr_db;
	int ret = read_signal_quality(&rsrp, &rsrq);

	if (ret < 0) {
		printk("Signal quality query failed\n");
	} else if (ret == 1) {
		printk("Signal quality: RSRP not detectable\n");
	} else {
		printk("Signal quality: RSRP %d dBm, RSRQ %.1f dB\n", rsrp, rsrq);
	}

	if (read_snr(&snr_db) == 0) {
		printk("Signal quality: SNR %d dB\n", snr_db);
	} else {
		printk("Signal quality: SNR not available\n");
	}
}

/* Unix epoch seconds (UTC) from the NCS date_time library. date_time obtains
 * the time from modem/network time (NITZ) first and falls back to NTP over the
 * IP connection, so it works even when the satellite network does not push time
 * directly. There is no battery RTC, so it returns 0 until a time has been
 * obtained from some source - the first send or two after boot may carry 0.
 */
static int64_t read_unix_time(void)
{
	int64_t unix_time_ms;

	if (date_time_now(&unix_time_ms) != 0) {
		return 0;
	}
	return unix_time_ms / 1000;
}

/* Render CONFIG_TEST_PAYLOADTEMPLATE into out, expanding the %-tokens documented
 * in Kconfig (%n %i %h %c %r %q %s %t %%). Unknown tokens are copied through
 * verbatim. Returns the payload length (excluding the NUL terminator), or -1 if
 * it does not fit in out_size.
 */
static int render_payload(char *out, size_t out_size, unsigned int counter)
{
	int rsrp = 0;
	double rsrq = 0.0;
	int snr_db = 0;
	bool have_signal = (read_signal_quality(&rsrp, &rsrq) == 0);
	bool have_snr = (read_snr(&snr_db) == 0);
	const char *p = CONFIG_TEST_PAYLOADTEMPLATE;
	size_t n = 0;

	while (*p != '\0') {
		int w;

		if (*p != '%') {
			if (n + 1 >= out_size) {
				return -1;
			}
			out[n++] = *p++;
			continue;
		}

		p++; /* consume '%' */
		switch (*p) {
		case 'n':
			w = snprintf(out + n, out_size - n, "%s", CONFIG_TEST_NAME);
			break;

		case 'i':
			w = snprintf(out + n, out_size - n, "%s", CONFIG_TAGO_DEVICE_TOKEN);
			break;
		case 'h':
			w = snprintf(out + n, out_size - n, "%s", CONFIG_TAGO_HASH);
			break;
        case 'c':
			w = snprintf(out + n, out_size - n, "%u", counter);
			break;
		case 'r':
			w = snprintf(out + n, out_size - n, "%d", have_signal ? rsrp : 0);
			break;
		case 'q':
			w = snprintf(out + n, out_size - n, "%.1f", have_signal ? rsrq : 0.0);
			break;
		case 't':
			w = snprintf(out + n, out_size - n, "%lld",
				     (long long)read_unix_time());
			break;
		case 's':
			w = snprintf(out + n, out_size - n, "%d", have_snr ? snr_db : 0);
			break;
		case '%':
			w = snprintf(out + n, out_size - n, "%%");
			break;
		case '\0':
			out[n] = '\0'; /* trailing '%' at end of template */
			return (int)n;
		default:
			w = snprintf(out + n, out_size - n, "%%%c", *p);
			break;
		}

		if (w < 0 || (size_t)w >= out_size - n) {
			return -1;
		}
		n += (size_t)w;
		p++;
	}

	out[n] = '\0';
	return (int)n;
}

/* Dump the full modem status line. %XMONITOR reports registration status plus
 * operator/PLMN, TAC, band, cell ID, RSRP and SNR in a single notification. The
 * field layout is variable (most fields are only present once registered), so
 * print the raw response rather than parsing each field individually.
 */
static void log_modem_status(void)
{
	char resp[160];
	int err;

	err = nrf_modem_at_cmd(resp, sizeof(resp), "AT%%XMONITOR");
	if (err) {
		printk("Modem status query failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return;
	}
	printk("Modem status: %s", resp);
}

/* Print the location source, current phase, position, and (dynamic mode) the
 * age and TTFF of the last GNSS fix. Shared by "gnss status" and "udp status".
 */
static void log_location(void)
{
	printk("Location mode: %s\n",
	       location_is_fixed ? "fixed (CONFIG_NTN_LOCATION)" :
				   "dynamic (internal GNSS)");
	printk("Phase: %s\n", phase_str(app_phase));
	printk("Network: %s%s\n", svc_name[link_net],
	       tn_fallback ? " (cellular attach failed; satellite fallback)" : "");
	printk("Position: lat %.6f, lon %.6f, alt %.1f m\n",
	       loc_lat, loc_lon, (double)loc_alt);

	if (location_is_fixed) {
		return;
	}

	if (last_fix_uptime > 0) {
		printk("Last GNSS fix: %lld s ago, TTFF %d s\n",
		       (k_uptime_get() - last_fix_uptime) / 1000, last_ttff_s);
	} else {
		printk("Last GNSS fix: none yet\n");
	}
}

/* Shell command: report the location source, phase, and last GNSS fix. */
static int cmd_gnss_status(const struct shell *sh, size_t argc, char **argv)
{
	ARG_UNUSED(sh);
	ARG_UNUSED(argc);
	ARG_UNUSED(argv);

	log_location();

	return 0;
}

/* Shell command: send a text string over the open UDP socket and print any
 * reply. Multi-word strings must be quoted, e.g. udp send "Hello, World!".
 */
static int cmd_udp_send(const struct shell *sh, size_t argc, char **argv)
{
	if (udp_fd < 0) {
		shell_error(sh, "UDP socket not ready (not registered yet)");
		return -ENOEXEC;
	}

	udp_send_and_recv(udp_fd, argv[1], strlen(argv[1]));

	return 0;
}

/* Shell command: report the current satellite link quality and modem status. */
static int cmd_udp_status(const struct shell *sh, size_t argc, char **argv)
{
	ARG_UNUSED(sh);
	ARG_UNUSED(argc);
	ARG_UNUSED(argv);

	log_signal_quality();
	log_modem_status();
	log_location();
	log_tally();

	return 0;
}

SHELL_STATIC_SUBCMD_SET_CREATE(udp_subcmds,
	SHELL_CMD_ARG(send, NULL,
		      "Send a text string over UDP. Usage: udp send <text>",
		      cmd_udp_send, 2, 0),
	SHELL_CMD(status, NULL,
		  "Report link quality (+CESQ), modem status (%XMONITOR), and location.",
		  cmd_udp_status),
	SHELL_SUBCMD_SET_END
);
SHELL_CMD_REGISTER(udp, &udp_subcmds, "UDP commands", NULL);

SHELL_STATIC_SUBCMD_SET_CREATE(gnss_subcmds,
	SHELL_CMD(status, NULL,
		  "Report location source, phase, position, and last GNSS fix.",
		  cmd_gnss_status),
	SHELL_SUBCMD_SET_END
);
SHELL_CMD_REGISTER(gnss, &gnss_subcmds, "GNSS/location commands", NULL);

/* Wait before retrying after an attach fails outright (rather than being
 * abandoned for a control-pin change), so a persistent error does not spin.
 */
#define LINK_RETRY_DELAY_S	30

/* attach_link() result: abandoned because the pins now select another network. */
#define LINK_ATTACH_PREEMPTED	1

/* Cellular: select the configured terrestrial system mode (GNSS enabled
 * alongside, as it coexists with terrestrial access) and replace the NTN band
 * lock left by a satellite attach. Called at CFUN=0. Returns 0 or -1.
 */
static int prepare_tn(void)
{
	const char *sysmode = IS_ENABLED(CONFIG_LINK_TN_MODE_NBIOT) ? "0,1,1,0" :
								      "1,0,1,0";
	int err;

	err = nrf_modem_at_printf("AT%%XSYSTEMMODE=%s", sysmode);
	if (err) {
		printk("Set cellular system mode failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}

	if (strlen(CONFIG_LINK_TN_BAND_LIST) > 0) {
		err = nrf_modem_at_printf("AT%%XBANDLOCK=2,,\"%s\"",
					  CONFIG_LINK_TN_BAND_LIST);
	} else {
		err = nrf_modem_at_printf("AT%%XBANDLOCK=0");
	}
	if (err) {
		printk("Cellular band lock failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}
	printk("Cellular %s, bands: %s\n",
	       IS_ENABLED(CONFIG_LINK_TN_MODE_NBIOT) ? "NB-IoT" : "LTE-M",
	       strlen(CONFIG_LINK_TN_BAND_LIST) > 0 ? CONFIG_LINK_TN_BAND_LIST : "all");

	return 0;
}

/* Satellite: make sure there is a usable position (dynamic mode acquires one
 * from GNSS if there is none yet or it has outlived its validity), then select
 * NTN NB-IoT, lock the NTN bands and seed the position so satellite acquisition
 * can start. Called at CFUN=0. Returns 0 or -1.
 */
static int prepare_ntn(void)
{
	int err;

	if (!location_is_fixed &&
	    (last_fix_uptime == 0 ||
	     (CONFIG_NTN_LOCATION_VALIDITY_S > 0 &&
	      (k_uptime_get() - last_fix_uptime) >
		      (int64_t)CONFIG_NTN_LOCATION_VALIDITY_S * 1000))) {
		if (acquire_gnss_location() != 0) {
			printk("GNSS acquisition failed\n");
			return -1;
		}
		app_phase = PHASE_ATTACHING;
	}

	/* All other systems must be 0 for the 5th parameter to enable NTN. */
	err = nrf_modem_at_printf("AT%%XSYSTEMMODE=0,0,0,0,1");
	if (err) {
		printk("Set NTN system mode failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}

	/* Lock to the NTN MSS bands. Must be done while in CFUN=0, otherwise it
	 * returns +CME ERROR 518. The band_list form is required: bands 255/256 are
	 * above the 88-bit band_mask range.
	 */
	err = nrf_modem_at_printf("AT%%XBANDLOCK=2,,\"%s\"", CONFIG_NTN_BAND_LIST);
	if (err) {
		printk("NTN band lock failed, type: %d, error: %d\n",
		       nrf_modem_at_err_type(err), nrf_modem_at_err(err));
		return -1;
	}
	printk("Locked to NTN bands %s\n", CONFIG_NTN_BAND_LIST);

	return set_modem_location(loc_lat, loc_lon, loc_alt,
				  CONFIG_NTN_LOCATION_VALIDITY_S) == 0 ? 0 : -1;
}

/* Wait for registration on net, checking the control pins every second so a
 * pin change abandons the attach at once. timeout_s 0 waits indefinitely.
 * Returns 0 when registered, LINK_ATTACH_PREEMPTED if the pins now select
 * another network, -1 on timeout.
 */
static int wait_registered(enum svc_net net, int timeout_s)
{
	int64_t start = k_uptime_get();

	while (k_sem_take(&lte_connected, K_SECONDS(1)) != 0) {
		if (link_choose() != net) {
			printk("%s attach abandoned: control pins changed\n",
			       svc_name[net]);
			return LINK_ATTACH_PREEMPTED;
		}
		if (timeout_s > 0 &&
		    (k_uptime_get() - start) > (int64_t)timeout_s * 1000) {
			printk("%s attach timed out after %d s\n", svc_name[net],
			       timeout_s);
			return -1;
		}
	}
	return 0;
}

/* Bring up the UDP link on net: CFUN=0 -> system mode + band lock (+ position
 * for satellite) -> connect -> PDN + socket. Returns 0 on success,
 * LINK_ATTACH_PREEMPTED if abandoned for a control-pin change, -1 on failure.
 * The modem is left at CFUN=0 on any failure.
 */
static int attach_link(enum svc_net net)
{
	int err, cid, pdn_id;

	printk("Attaching to %s\n", svc_name[net]);
	app_phase = PHASE_ATTACHING;
	refix_requested = false;

	/* System mode and band lock can only change at CFUN=0. */
	(void)nrf_modem_at_printf("AT+CFUN=0");
	if ((net == SVC_TN ? prepare_tn() : prepare_ntn()) != 0) {
		return -1;
	}

	cid = udp_pdn_setup();
	if (cid == -1) {
		return -1;
	}

	k_sem_reset(&lte_connected);
	modem_connect();
	err = wait_registered(net, net == SVC_TN ? CONFIG_LINK_ATTACH_TIMEOUT_TN_S :
						   CONFIG_LINK_ATTACH_TIMEOUT_NTN_S);
	if (err) {
		lte_lc_power_off();	/* stop searching */
		return err;
	}

	log_signal_quality();
	log_modem_status();

	pdn_id = udp_pdn_activate(cid);
	if (pdn_id != -1) {
		udp_fd = udp_socket_setup(pdn_id);
	}
	if (pdn_id == -1 || udp_fd == -1) {
		udp_fd = -1;
		lte_lc_power_off();
		return -1;
	}

	link_net = net;
	app_phase = PHASE_CONNECTED;
	printk("%s link up\n", svc_name[net]);
	return 0;
}

/* Tear down the current link (close socket, modem to CFUN=0) before switching
 * networks or acquiring a fresh GNSS fix.
 */
static void detach_link(void)
{
	if (udp_fd >= 0) {
		udp_socket_close(udp_fd);
		udp_fd = -1;
	}
	lte_lc_power_off();
	if (link_net != SVC_NONE) {
		printk("%s link down\n", svc_name[link_net]);
	}
	link_net = SVC_NONE;
}

/* Detach from whatever is up and attach to want (SVC_NONE leaves the radio
 * off). A failed cellular attach starts the satellite fallback. Returns the
 * attach_link() result.
 */
static int link_switch(enum svc_net want)
{
	int err;

	detach_link();
	if (want == SVC_NONE) {
		printk("Both networks grounded by control pins; radio off\n");
		app_phase = PHASE_NO_SERVICE;
		return 0;
	}

	err = attach_link(want);
	if (want == SVC_TN) {
		tn_fallback = (err == -1);
		if (tn_fallback) {
			tn_fail_uptime = k_uptime_get();
			if (!svc_disabled(SVC_NTN)) {
				printk("Cellular attach failed; using satellite, "
				       "cellular retry in %d s\n",
				       CONFIG_LINK_TN_PROBE_INTERVAL_S);
			}
		}
	}
	return err;
}

int main(void)
{
	unsigned int counter = 0;

	printk("LooUQ MTC2-N9151 cellular/NTN UDP sample started\n");
	if (strlen(CONFIG_TAGO_DEVICE_TOKEN) == 0 || strlen(CONFIG_TAGO_HASH) == 0) {
		printk("WARNING: TagoIO token/hash not set; copy secrets.conf.example "
		       "to secrets.conf and rebuild\n");
	}
	svc_pins_init();
	modem_init();

	/* CONFIG_NTN_LOCATION set -> fixed position; empty -> acquire from GNSS
	 * before the first satellite attach.
	 */
	location_is_fixed =
		(parse_location(CONFIG_NTN_LOCATION, &loc_lat, &loc_lon, &loc_alt) == 0);

	if (location_is_fixed) {
		printk("Using fixed location from CONFIG_NTN_LOCATION: "
		       "lat %.6f, lon %.6f, alt %.1f m\n",
		       loc_lat, loc_lon, (double)loc_alt);
	} else {
		printk("CONFIG_NTN_LOCATION empty; satellite position comes from internal GNSS\n");
	}

	/* Send a freshly rendered CONFIG_TEST_TEMPLATE payload every
	 * CONFIG_TEST_INTERVAL seconds on whichever network the control pins
	 * select. The socket stays open between sends, so "udp send <text>"
	 * remains available for manual messages.
	 */
	printk("Sending every %d s. Manual send still available: udp send <text>\n",
	       CONFIG_TEST_INTERVAL);

	for (;;) {
		enum svc_net want = link_choose();

		if (want == SVC_NONE) {
			if (app_phase != PHASE_NO_SERVICE) {
				(void)link_switch(SVC_NONE);
			}
			k_sleep(K_SECONDS(1));
			continue;
		}

		if (want != link_net) {
			int err = link_switch(want);

			if (err == LINK_ATTACH_PREEMPTED) {
				continue;
			}
			if (err) {
				/* Back off before retrying; a pin change (or the
				 * cellular fallback) cuts the wait short.
				 */
				for (int s = 0; s < LINK_RETRY_DELAY_S &&
						link_choose() == want; s++) {
					k_sleep(K_SECONDS(1));
				}
				continue;
			}
		}

		char payload[256];
		int len = render_payload(payload, sizeof(payload), counter++);

		total_cycles++;
		if (len < 0) {
			printk("Payload does not fit buffer; check CONFIG_TEST_TEMPLATE\n");
		} else {
			udp_send_and_recv(udp_fd, payload, len);
		}
		log_tally();

		/* The modem asked for a fresh location and the cached fix is stale.
		 * Internal GNSS cannot run while NTN is active, so drop the link and
		 * re-acquire; the next pass re-attaches. (Satellite, dynamic mode.)
		 */
		if (link_net == SVC_NTN && !location_is_fixed && refix_requested) {
			printk("Refreshing GNSS location on modem request\n");
			refix_requested = false;
			detach_link();
			if (acquire_gnss_location() != 0) {
				printk("GNSS acquisition failed; keeping previous position\n");
			}
		}

		/* Sleep in 1 s steps so a control-pin change takes effect promptly
		 * instead of after a full send interval.
		 */
		for (int s = 0; s < CONFIG_TEST_INTERVAL && link_choose() == link_net; s++) {
			k_sleep(K_SECONDS(1));
		}
	}

	return 0;
}
