// =============================================================================
//  NTP Clock — ESP32-S3 MINI + 0.96" OLED
//  Copyright (c) 2026 eElectronicParts.com
//
//  Licensed under the MIT License (see bottom of file for full text).
//
//  You are free to use, modify, and redistribute this code, including in
//  commercial projects. If you share a modified version publicly (blog post,
//  YouTube, GitHub, Instructables, forum), a link back to the original is
//  appreciated but not required:
//
//    Original project: https://www.eelectronicparts.com/
//        
// Analog + Digital NTP Clock with RSS ticker, "On this day" cards,
// 1-px border, moving seconds bead, source badges, fetch indicators.
// Clock circle sits 1 px inside the border; news ticker has 2 px side
// margins and is raised 1 px so it no longer touches the bottom border.
// ESP32 + SSD1306 128x64 (I2C SDA=8, SCL=9, addr 0x3C)
// ===================================================
/*
 *  v.0 - small changes by Nicu FLORICA (niq_ro): rotate the display, decrease wifi power, Romania time
 *  v.1 - fara chenar, layout urcat pentru ecran bicolor albastru-galben
 * 
*/

#include <Wire.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <Fonts/TomThumb.h>
#include <WiFi.h>
#include <HTTPClient.h>
#include <WiFiClientSecure.h>
#include <time.h>
#include <math.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <freertos/semphr.h>

#include "history_events.h"

// ================== USER SETTINGS ==================
const char* WIFI_SSID = "bbk2";  //"YOUR_WIFI_SSID";
const char* WIFI_PASS = "internet2";  //"YOUR_WIFI_PASS";

#define TZ_EASTERN   "EST5EDT,M3.2.0,M11.1.0"
#define TZ_CENTRAL   "CST6CDT,M3.2.0,M11.1.0"
#define TZ_MOUNTAIN  "MST7MDT,M3.2.0,M11.1.0"
#define TZ_PACIFIC   "PST8PDT,M3.2.0,M11.1.0"
#define TZ_ROMANIA   "EET-2EEST,M3.5.0/3,M10.5.0/4"
const char* TIMEZONE = TZ_ROMANIA;

const char* NTP_SERVER = "pool.ntp.org";

const unsigned long RSS_REFRESH_MIN    = 15;
const int           HEADLINES_PER_FEED = 2;
const float         SCROLL_SPEED_PXS   = 30.0f;
const float         CARD_SPEED_FACTOR  = 0.70f; // card scroll speed factor
const unsigned long CARD_DWELL_MS      = 20000; // hold time for cards
const unsigned long FLASH_DURATION_MS  = 600;   // fetch-success dot
const unsigned long FETCH_ANIM_LINGER  = 1500;  // WiFi blink after fetch


#define SCREEN_WIDTH   128
#define SCREEN_HEIGHT  64
#define OLED_RESET     -1
#define OLED_ADDR      0x3C
#define SDA_PIN        8
#define SCL_PIN        9
Adafruit_SSD1306 display(SCREEN_WIDTH, SCREEN_HEIGHT, &Wire, OLED_RESET);

// Analog clock — R=24, CY=23. Bottom edge is y=47 (maxim pentru zona albastra)
const int16_t CX = 27;
const int16_t CY = 24;     // MODIFICAT: era 27
const int16_t R  = 23;     // MODIFICAT: era 25
const int16_t NUM_RAD   = 18;
const int16_t HOUR_LEN  = 11;
const int16_t MIN_LEN   = 19;
const int16_t SEC_LEN   = 22;
const int16_t HOUR_BASE = 3;
const int16_t MIN_BASE  = 2;

// Digital panel (TEXT_X_LEFT follows CX+R+4, so it auto-adjusts)
const int16_t TEXT_X_LEFT   = CX + R + 4;          // = 55
const int16_t TEXT_X_RIGHT  = SCREEN_WIDTH - 1;    // = 127
const int16_t PANEL_W       = TEXT_X_RIGHT - TEXT_X_LEFT + 1; // = 73
const int16_t ROW_Y[4]      = { 5, 16, 27, 38 };   // MODIFICAT: era { 6, 18, 30, 42 }
const int16_t SIGNAL_ICON_W = 11;

// News ticker
const int16_t NEWS_Y                = 56;   // MODIFICAT: era 55
const int16_t TICKER_MARGIN         = 1;    // MODIFICAT: era 3 (eliminat chenarul, nu mai avem nevoie de margine lata)
const unsigned long SCROLL_FRAME_MS = 50;

// Badge geometry (inverted text in a filled rectangle)
const int16_t BADGE_W       = 14;
const int16_t BADGE_H       = 8;
const int16_t BADGE_GAP     = 1;                        // trailing spacer
const int16_t BADGE_ADVANCE = BADGE_W + BADGE_GAP;      // = 15

// Marker bytes embedded in scroll strings
#define MARKER_BBC  '\001'
#define MARKER_NPR  '\002'
#define MARKER_AJ   '\003'
#define MARKER_HIST '\004'

// RSS feeds
struct RssFeed {
  const char* url;
  char        marker;
  const char* tag;
};
const RssFeed feeds[] = {
  { "https://feeds.bbci.co.uk/news/world/rss.xml", MARKER_BBC, "BBC" },
  { "https://feeds.npr.org/1001/rss.xml",           MARKER_NPR, "NPR" },
  { "https://www.aljazeera.com/xml/rss/all.xml",    MARKER_AJ,  "AJ"  },
};
const int NUM_FEEDS = sizeof(feeds) / sizeof(feeds[0]);

// ---- Shared state (dataMutex) ----
String         newsText     = "";
uint16_t       newsTextW    = 0;
bool           hasNews      = false;
unsigned long  nextRssFetch = 0;
SemaphoreHandle_t dataMutex = NULL;

// ---- UI state ----
enum TickerMode { TM_NEWS, TM_CARD };
TickerMode    tickerMode = TM_NEWS;

enum CardPhase { CP_ENTER, CP_DWELL, CP_EXIT, CP_LONG };
CardPhase     cardPhase;
String        cardText;
uint16_t      cardTextW      = 0;
int16_t       cardDwellX     = 0;
bool          cardFits       = false;
unsigned long cardPhaseStart = 0;

float         scrollX        = SCREEN_WIDTH;
unsigned long lastScrollTick = 0;
unsigned long lastFrame      = 0;

// ---- Diagnostics (atomic via volatile) ----
volatile unsigned long fetchAnimUntil = 0;
volatile unsigned long newsFlashUntil = 0;

// =================================================================
//                            HELPERS
// =================================================================

void showMessage(const String& l1, const String& l2 = "") {
  if (dataMutex && xSemaphoreTake(dataMutex, portMAX_DELAY) != pdTRUE) return;
  display.clearDisplay();
  display.setFont();
  display.setTextColor(SSD1306_WHITE);
  display.setTextSize(1);
  display.setCursor(0, 10); display.println(l1);
  if (l2.length()) { display.setCursor(0, 25); display.println(l2); }
  display.display();
  if (dataMutex) xSemaphoreGive(dataMutex);
}

static inline void polar(float angleDeg, int16_t length, int16_t& x, int16_t& y) {
  float a = (angleDeg - 90.0f) * DEG_TO_RAD;
  x = CX + (int16_t)lroundf(length * cosf(a));
  y = CY + (int16_t)lroundf(length * sinf(a));
}

void drawWedgeHand(float angleDeg, int16_t length, int16_t baseHalfW) {
  float a = (angleDeg - 90.0f) * DEG_TO_RAD;
  float cs = cosf(a), sn = sinf(a);
  int16_t tipX = CX + (int16_t)lroundf(length * cs);
  int16_t tipY = CY + (int16_t)lroundf(length * sn);
  float px = -sn, py = cs;
  int16_t b1X = CX + (int16_t)lroundf(baseHalfW * px);
  int16_t b1Y = CY + (int16_t)lroundf(baseHalfW * py);
  int16_t b2X = CX - (int16_t)lroundf(baseHalfW * px);
  int16_t b2Y = CY - (int16_t)lroundf(baseHalfW * py);
  display.fillTriangle(tipX, tipY, b1X, b1Y, b2X, b2Y, SSD1306_WHITE);
}

void drawHourNumber(int n, float angleDeg, int16_t rad) {
  String s = String(n);
  display.setFont(&TomThumb); display.setTextSize(1);
  int16_t x1, y1; uint16_t w, h;
  display.getTextBounds(s, 0, 0, &x1, &y1, &w, &h);
  float a = (angleDeg - 90.0f) * DEG_TO_RAD;
  int16_t px = CX + (int16_t)lroundf(rad * cosf(a));
  int16_t py = CY + (int16_t)lroundf(rad * sinf(a));
  display.setCursor(px - (w / 2) - x1, py - (h / 2) - y1);
  display.print(s);
}

// Signal icon: normally RSSI-driven bars; during fetch the entire icon
// BLINKS on/off (clearly different from any RSSI animation).
void drawSignalIcon(int16_t x, int16_t y, int32_t rssi, bool animate) {
  if (animate) {
    bool on = ((millis() / 200) % 2) == 0;
    if (!on) return;
    for (int i = 0; i < 4; i++) {
      int16_t bx = x + i * 3;
      int16_t bh = (i + 1) * 2;
      int16_t by = y + (8 - bh);
      display.fillRect(bx, by, 2, bh, SSD1306_WHITE);
    }
    return;
  }
  int bars;
  if      (rssi >= -55) bars = 4;
  else if (rssi >= -65) bars = 3;
  else if (rssi >= -75) bars = 2;
  else if (rssi >= -85) bars = 1;
  else                  bars = 0;
  for (int i = 0; i < 4; i++) {
    int16_t bx = x + i * 3;
    int16_t bh = (i + 1) * 2;
    int16_t by = y + (8 - bh);
    if (i < bars) display.fillRect(bx, by, 2, bh, SSD1306_WHITE);
    else          display.drawRect(bx, by, 2, bh, SSD1306_WHITE);
  }
}

void drawCenteredInPanel(const String& s, int16_t y) {
  display.setFont(); display.setTextSize(1); display.setTextColor(SSD1306_WHITE);
  int16_t x1, y1; uint16_t w, h;
  display.getTextBounds(s, 0, 0, &x1, &y1, &w, &h);
  int16_t x = TEXT_X_LEFT + (PANEL_W - (int16_t)w) / 2;
  display.setCursor(x, y); display.print(s);
}

// Inverted-text source badge: 14x8 white box, TomThumb text in black.
void drawBadge(int16_t x, int16_t y, const char* label) {
  display.fillRect(x, y, BADGE_W, BADGE_H, SSD1306_WHITE);
  display.setFont(&TomThumb);
  display.setTextSize(1);
  display.setTextColor(SSD1306_BLACK);
  int16_t x1, y1; uint16_t w, h;
  display.getTextBounds(label, 0, 0, &x1, &y1, &w, &h);
  int16_t tx = x + (BADGE_W - (int16_t)w) / 2 - x1;
  int16_t ty = y + (BADGE_H - (int16_t)h) / 2 - y1;
  display.setCursor(tx, ty);
  display.print(label);
  display.setFont();
  display.setTextColor(SSD1306_WHITE);
}

// Scroll rendering: default-font text + badge markers. Characters/badges
// are only drawn if ENTIRELY within [LEFT_LIMIT .. RIGHT_LIMIT], which
// places them cleanly inside the border with 2 px of visible margin.
void drawScrollSegment(const String& s, int16_t startX, int16_t y) {
  display.setFont(); display.setTextSize(1); display.setTextColor(SSD1306_WHITE);
  const int16_t LEFT_LIMIT  = TICKER_MARGIN;                // 1
  const int16_t RIGHT_LIMIT = SCREEN_WIDTH - TICKER_MARGIN;  // 127

  int16_t x = startX;
  for (size_t i = 0; i < s.length(); i++) {
    uint8_t c = (uint8_t)s[i];
    if (c >= 1 && c <= 4) {
      if (x >= LEFT_LIMIT && x + BADGE_W <= RIGHT_LIMIT) {
        const char* lbl =
          (c == 1) ? "BBC" :
          (c == 2) ? "NPR" :
          (c == 3) ? "AJ"  : "HIST";
        drawBadge(x, y, lbl);
      }
      x += BADGE_ADVANCE;
    } else {
      if (x >= LEFT_LIMIT && x + 6 <= RIGHT_LIMIT) {
        display.setCursor(x, y);
        display.write(c);
      }
      x += 6;
    }
    if (x > RIGHT_LIMIT) break;
  }
}

uint16_t computeScrollWidth(const String& s) {
  uint16_t w = 0;
  for (size_t i = 0; i < s.length(); i++) {
    uint8_t c = (uint8_t)s[i];
    w += (c >= 1 && c <= 4) ? BADGE_ADVANCE : 6;
  }
  return w;
}

// Chenarul a fost eliminat complet
// void drawBorder() {
//   display.drawRect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, SSD1306_WHITE);
// }

// =================================================================
//                    RSS FETCH & HTML DECODE
// =================================================================

// Map a Unicode code point to an ASCII approximation and append to `out`.
// Covers Latin accents, smart punctuation, currencies, arrows, and a few
// common symbols. Anything we don't recognize becomes '?' so at least the
// length is stable and you notice.
static void appendAsAscii(String& out, uint32_t cp) {
  if (cp >= 0x20 && cp <= 0x7E) { out += (char)cp; return; }

  switch (cp) {
    // Whitespace / controls
    case 0x00A0: case 0x2000: case 0x2001: case 0x2002: case 0x2003:
    case 0x2004: case 0x2005: case 0x2006: case 0x2007: case 0x2008:
    case 0x2009: case 0x200A: case 0x202F: case 0x205F:
      out += ' '; return;

    // Latin-1 punctuation & symbols
    case 0x00A1: out += '!';    return;
    case 0x00A2: out += 'c';    return;
    case 0x00A3: out += "GBP";  return;
    case 0x00A5: out += "JPY";  return;
    case 0x00A7: out += '$';    return;
    case 0x00A9: out += "(c)";  return;
    case 0x00AA: out += 'a';    return;
    case 0x00AB: out += '"';    return;
    case 0x00AE: out += "(R)";  return;
    case 0x00B0: out += " deg"; return;
    case 0x00B1: out += "+/-";  return;
    case 0x00B4: out += '\'';   return;
    case 0x00B7: out += '.';    return;
    case 0x00BA: out += 'o';    return;
    case 0x00BB: out += '"';    return;
    case 0x00BC: out += "1/4";  return;
    case 0x00BD: out += "1/2";  return;
    case 0x00BE: out += "3/4";  return;
    case 0x00BF: out += '?';    return;

    // Accented letters -> base letter
    case 0x00C0: case 0x00C1: case 0x00C2: case 0x00C3:
    case 0x00C4: case 0x00C5:                  out += 'A';  return;
    case 0x00C6:                               out += "AE"; return;
    case 0x00C7:                               out += 'C';  return;
    case 0x00C8: case 0x00C9: case 0x00CA:
    case 0x00CB:                               out += 'E';  return;
    case 0x00CC: case 0x00CD: case 0x00CE:
    case 0x00CF:                               out += 'I';  return;
    case 0x00D0:                               out += 'D';  return;
    case 0x00D1:                               out += 'N';  return;
    case 0x00D2: case 0x00D3: case 0x00D4:
    case 0x00D5: case 0x00D6: case 0x00D8:     out += 'O';  return;
    case 0x00D7:                               out += 'x';  return;
    case 0x00D9: case 0x00DA: case 0x00DB:
    case 0x00DC:                               out += 'U';  return;
    case 0x00DD:                               out += 'Y';  return;
    case 0x00DE:                               out += "Th"; return;
    case 0x00DF:                               out += "ss"; return;
    case 0x00E0: case 0x00E1: case 0x00E2: case 0x00E3:
    case 0x00E4: case 0x00E5:                  out += 'a';  return;
    case 0x00E6:                               out += "ae"; return;
    case 0x00E7:                               out += 'c';  return;
    case 0x00E8: case 0x00E9: case 0x00EA:
    case 0x00EB:                               out += 'e';  return;
    case 0x00EC: case 0x00ED: case 0x00EE:
    case 0x00EF:                               out += 'i';  return;
    case 0x00F0:                               out += 'd';  return;
    case 0x00F1:                               out += 'n';  return;
    case 0x00F2: case 0x00F3: case 0x00F4:
    case 0x00F5: case 0x00F6: case 0x00F8:     out += 'o';  return;
    case 0x00F7:                               out += '/';  return;
    case 0x00F9: case 0x00FA: case 0x00FB:
    case 0x00FC:                               out += 'u';  return;
    case 0x00FD: case 0x00FF:                  out += 'y';  return;
    case 0x00FE:                               out += "th"; return;

    // Latin Extended-A (Central/Eastern European)
    case 0x0100: case 0x0102: case 0x0104:          out += 'A'; return;
    case 0x0101: case 0x0103: case 0x0105:          out += 'a'; return;
    case 0x0106: case 0x0108: case 0x010A:
    case 0x010C:                                     out += 'C'; return;
    case 0x0107: case 0x0109: case 0x010B:
    case 0x010D:                                     out += 'c'; return;
    case 0x010E: case 0x0110:                        out += 'D'; return;
    case 0x010F: case 0x0111:                        out += 'd'; return;
    case 0x0112: case 0x0114: case 0x0116:
    case 0x0118: case 0x011A:                        out += 'E'; return;
    case 0x0113: case 0x0115: case 0x0117:
    case 0x0119: case 0x011B:                        out += 'e'; return;
    case 0x011C: case 0x011E: case 0x0120:
    case 0x0122:                                     out += 'G'; return;
    case 0x011D: case 0x011F: case 0x0121:
    case 0x0123:                                     out += 'g'; return;
    case 0x0139: case 0x013B: case 0x013D:
    case 0x013F: case 0x0141:                        out += 'L'; return;
    case 0x013A: case 0x013C: case 0x013E:
    case 0x0140: case 0x0142:                        out += 'l'; return;
    case 0x0143: case 0x0145: case 0x0147:           out += 'N'; return;
    case 0x0144: case 0x0146: case 0x0148:           out += 'n'; return;
    case 0x014C: case 0x014E: case 0x0150:           out += 'O'; return;
    case 0x014D: case 0x014F: case 0x0151:           out += 'o'; return;
    case 0x0154: case 0x0156: case 0x0158:           out += 'R'; return;
    case 0x0155: case 0x0157: case 0x0159:           out += 'r'; return;
    case 0x015A: case 0x015C: case 0x015E:
    case 0x0160:                                     out += 'S'; return;
    case 0x015B: case 0x015D: case 0x015F:
    case 0x0161:                                     out += 's'; return;
    case 0x0164: case 0x0166:                        out += 'T'; return;
    case 0x0165: case 0x0167:                        out += 't'; return;
    case 0x0168: case 0x016A: case 0x016C:
    case 0x016E: case 0x0170: case 0x0172:           out += 'U'; return;
    case 0x0169: case 0x016B: case 0x016D:
    case 0x016F: case 0x0171: case 0x0173:           out += 'u'; return;
    case 0x0174:                                     out += 'W'; return;
    case 0x0175:                                     out += 'w'; return;
    case 0x0176: case 0x0178:                        out += 'Y'; return;
    case 0x0177:                                     out += 'y'; return;
    case 0x0179: case 0x017B: case 0x017D:           out += 'Z'; return;
    case 0x017A: case 0x017C: case 0x017E:           out += 'z'; return;

    // General Punctuation (U+2000 block) — THE big one for RSS
    case 0x2010: case 0x2011: case 0x2012:
    case 0x2013:                                 out += '-';     return;
    case 0x2014: case 0x2015:                    out += "--";    return;
    case 0x2018: case 0x2019: case 0x201A:
    case 0x201B:                                 out += '\'';    return;
    case 0x201C: case 0x201D: case 0x201E:
    case 0x201F:                                 out += '"';     return;
    case 0x2020: case 0x2021:                    out += '+';     return;
    case 0x2022: case 0x2023: case 0x25AA:
    case 0x25CF: case 0x2043:                    out += '*';     return;
    case 0x2026:                                 out += "...";   return;
    case 0x2030:                                 out += "o/oo";  return;
    case 0x2032: case 0x2035:                    out += '\'';    return;
    case 0x2033: case 0x2036:                    out += '"';     return;
    case 0x2039:                                 out += '<';     return;
    case 0x203A:                                 out += '>';     return;
    case 0x203C:                                 out += "!!";    return;
    case 0x2047:                                 out += "??";    return;
    case 0x2048:                                 out += "?!";    return;

    // Currency
    case 0x20A4:                                 out += "GBP";   return;
    case 0x20AC:                                 out += "EUR";   return;
    case 0x20B9:                                 out += "INR";   return;
    case 0x20BD:                                 out += "RUB";   return;
    case 0x20BF:                                 out += "BTC";   return;

    // Letterlike / arrows / math
    case 0x2116:                                 out += "No.";   return;
    case 0x2122:                                 out += "(TM)";  return;
    case 0x2190:                                 out += "<-";    return;
    case 0x2191:                                 out += "^";     return;
    case 0x2192:                                 out += "->";    return;
    case 0x2193:                                 out += "v";     return;
    case 0x2194:                                 out += "<->";   return;
    case 0x21D2:                                 out += "=>";    return;
    case 0x21D4:                                 out += "<=>";   return;
    case 0x2212:                                 out += '-';     return;
    case 0x2260:                                 out += "!=";    return;
    case 0x2264:                                 out += "<=";    return;
    case 0x2265:                                 out += ">=";    return;
    case 0x2713: case 0x2714:                    out += 'v';     return;
    case 0x2717: case 0x2718:                    out += 'x';     return;

    default:
      out += '?';
      return;
  }
}

// Decode HTML/XML entities (named, decimal, hex) and raw UTF-8 bytes in
// one pass. Output is pure printable ASCII so the default font can draw it.
// Stray tags (rare in RSS <title>) are stripped at the end.
String decodeEntities(const String& in) {
  String out;
  out.reserve(in.length());

  size_t i = 0;
  while (i < in.length()) {
    uint8_t c = (uint8_t)in[i];

    // --- HTML entity? -----------------------------------------------
    if (c == '&') {
      int semi = in.indexOf(';', i + 1);
      if (semi > 0 && semi - i <= 10) {
        String ent = in.substring(i + 1, semi);
        uint32_t cp = 0;
        bool decoded = false;

        if (ent.length() > 1 && ent[0] == '#') {
          // Numeric entity — decimal or hex.
          if (ent[1] == 'x' || ent[1] == 'X') {
            cp = strtoul(ent.c_str() + 2, NULL, 16);
          } else {
            cp = strtoul(ent.c_str() + 1, NULL, 10);
          }
          decoded = (cp > 0);
        } else {
          // Named entity — short table of the ones RSS feeds actually use.
          if      (ent == "amp")    { cp = '&';    decoded = true; }
          else if (ent == "lt")     { cp = '<';    decoded = true; }
          else if (ent == "gt")     { cp = '>';    decoded = true; }
          else if (ent == "quot")   { cp = '"';    decoded = true; }
          else if (ent == "apos")   { cp = '\'';   decoded = true; }
          else if (ent == "nbsp")   { cp = ' ';    decoded = true; }
          else if (ent == "ndash")  { cp = 0x2013; decoded = true; }
          else if (ent == "mdash")  { cp = 0x2014; decoded = true; }
          else if (ent == "hellip") { cp = 0x2026; decoded = true; }
          else if (ent == "lsquo")  { cp = 0x2018; decoded = true; }
          else if (ent == "rsquo")  { cp = 0x2019; decoded = true; }
          else if (ent == "ldquo")  { cp = 0x201C; decoded = true; }
          else if (ent == "rdquo")  { cp = 0x201D; decoded = true; }
          else if (ent == "sbquo")  { cp = 0x201A; decoded = true; }
          else if (ent == "bdquo")  { cp = 0x201E; decoded = true; }
          else if (ent == "bull")   { cp = 0x2022; decoded = true; }
          else if (ent == "middot") { cp = 0x00B7; decoded = true; }
          else if (ent == "copy")   { cp = 0x00A9; decoded = true; }
          else if (ent == "reg")    { cp = 0x00AE; decoded = true; }
          else if (ent == "trade")  { cp = 0x2122; decoded = true; }
          else if (ent == "euro")   { cp = 0x20AC; decoded = true; }
          else if (ent == "pound")  { cp = 0x00A3; decoded = true; }
          else if (ent == "yen")    { cp = 0x00A5; decoded = true; }
          else if (ent == "cent")   { cp = 0x00A2; decoded = true; }
          else if (ent == "deg")    { cp = 0x00B0; decoded = true; }
          else if (ent == "plusmn") { cp = 0x00B1; decoded = true; }
          else if (ent == "times")  { cp = 0x00D7; decoded = true; }
          else if (ent == "divide") { cp = 0x00F7; decoded = true; }
          else if (ent == "laquo")  { cp = 0x00AB; decoded = true; }
          else if (ent == "raquo")  { cp = 0x00BB; decoded = true; }
          else if (ent == "iexcl")  { cp = 0x00A1; decoded = true; }
          else if (ent == "iquest") { cp = 0x00BF; decoded = true; }
          else if (ent == "eacute") { cp = 0x00E9; decoded = true; }
          else if (ent == "Eacute") { cp = 0x00C9; decoded = true; }
          else if (ent == "aacute") { cp = 0x00E1; decoded = true; }
          else if (ent == "iacute") { cp = 0x00ED; decoded = true; }
          else if (ent == "oacute") { cp = 0x00F3; decoded = true; }
          else if (ent == "uacute") { cp = 0x00FA; decoded = true; }
          else if (ent == "ntilde") { cp = 0x00F1; decoded = true; }
          else if (ent == "Ntilde") { cp = 0x00D1; decoded = true; }
        }

        if (decoded) {
          appendAsAscii(out, cp);
          i = semi + 1;
          continue;
        }
      }
      // Fall through: treat '&' as a literal if the entity didn't parse.
    }

    // --- UTF-8 multi-byte sequence? --------------------------------
    if (c >= 0x80) {
      uint32_t cp = 0;
      int len = 0;
      if      ((c & 0xE0) == 0xC0) { cp = c & 0x1F; len = 2; }
      else if ((c & 0xF0) == 0xE0) { cp = c & 0x0F; len = 3; }
      else if ((c & 0xF8) == 0xF0) { cp = c & 0x07; len = 4; }
      else                         { i++; continue; } // bad start byte, skip

      bool valid = true;
      for (int k = 1; k < len; k++) {
        if (i + k >= in.length() ||
            ((uint8_t)in[i + k] & 0xC0) != 0x80) { valid = false; break; }
        cp = (cp << 6) | ((uint8_t)in[i + k] & 0x3F);
      }
      if (valid) { appendAsAscii(out, cp); i += len; }
      else       { i++; }
      continue;
    }

    // --- Plain ASCII ----------------------------------------------
    if (c >= 0x20 && c <= 0x7E)       out += (char)c;
    else if (c == '\n' || c == '\r' ||
             c == '\t')               out += ' ';
    // else: strip control byte silently
    i++;
  }

  // Strip any stray tags (rare in <title>, but harmless safety pass)
  while (true) {
    int lt = out.indexOf('<');     if (lt < 0) break;
    int gt = out.indexOf('>', lt); if (gt < 0) break;
    out.remove(lt, gt - lt + 1);
  }
  return out;
}

String parseHeadlines(const String& xml, char marker, int maxN) {
  String out;
  int pos = 0, count = 0;
  while (count < maxN) {
    int itemStart = xml.indexOf("<item", pos); if (itemStart < 0) break;
    int itemEnd   = xml.indexOf("</item>", itemStart); if (itemEnd < 0) break;
    int tOpen = xml.indexOf("<title", itemStart);
    if (tOpen < 0 || tOpen > itemEnd) { pos = itemEnd + 7; continue; }
    int tContent = xml.indexOf('>', tOpen);
    if (tContent < 0) { pos = itemEnd + 7; continue; }
    tContent++;
    int tClose = xml.indexOf("</title>", tContent);
    if (tClose < 0 || tClose > itemEnd) { pos = itemEnd + 7; continue; }

    String title = xml.substring(tContent, tClose);
    title.replace("<![CDATA[", ""); title.replace(">>", "");
    title.trim();
    title = decodeEntities(title);

    if (title.length() > 0) {
      if (out.length() > 0) out += "   ";
      out += marker;
      out += ' ';
      out += title;
      count++;
    }
    pos = itemEnd + 7;
  }
  return out;
}

String fetchFeed(const RssFeed& feed) {
  WiFiClientSecure client;
  client.setInsecure(); client.setTimeout(8000);
  HTTPClient http;
  http.setTimeout(8000);
  http.setUserAgent("ESP32-Clock/1.0");
  http.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
  if (!http.begin(client, feed.url)) return "";
  int code = http.GET();
  if (code != HTTP_CODE_OK) {
    Serial.printf("Feed %s HTTP %d\n", feed.tag, code);
    http.end(); return "";
  }
  String body = http.getString();
  http.end();
  return parseHeadlines(body, feed.marker, HEADLINES_PER_FEED);
}

bool fetchNews() {
  fetchAnimUntil = millis() + 60000UL;   // animate "indefinitely" during fetch
  String combined;
  for (int i = 0; i < NUM_FEEDS; i++) {
    String chunk = fetchFeed(feeds[i]);
    if (chunk.length() > 0) {
      if (combined.length() > 0) combined += "   ";
      combined += chunk;
    }
    vTaskDelay(pdMS_TO_TICKS(100));
  }
  bool ok = (combined.length() > 0);
  if (ok) {
    combined += "   ";
    uint16_t width = computeScrollWidth(combined);
    if (xSemaphoreTake(dataMutex, portMAX_DELAY) == pdTRUE) {
      newsText  = combined;
      newsTextW = width;
      hasNews   = true;
      xSemaphoreGive(dataMutex);
    }
    newsFlashUntil = millis() + FLASH_DURATION_MS;
    Serial.printf("News updated: %u chars, %u px\n",
                  (unsigned)combined.length(), (unsigned)width);
  }
  fetchAnimUntil = millis() + FETCH_ANIM_LINGER;   // linger after finish
  return ok;
}

// =================================================================
//                 ON-THIS-DAY CARD BUILDER
// =================================================================

String buildOnThisDay(const struct tm& t) {
  int m = t.tm_mon + 1, d = t.tm_mday;
  const HistEvent* e = getNextCardEvent(m, d);
  if (!e) return "";

  char buf[72];
  bool todaysEvent = (e->month == m && e->day == d);
  static const char* const monthAbbr[] = {
    "","Jan","Feb","Mar","Apr","May","Jun",
    "Jul","Aug","Sep","Oct","Nov","Dec"
  };
  if (todaysEvent) {
    if (e->year > 0) snprintf(buf, sizeof(buf), "%u: %s", (unsigned)e->year, e->text);
    else             snprintf(buf, sizeof(buf), "%s", e->text);
  } else {
    if (e->year > 0) snprintf(buf, sizeof(buf), "%s %d, %u: %s",
                              monthAbbr[e->month], e->day, (unsigned)e->year, e->text);
    else             snprintf(buf, sizeof(buf), "%s %d: %s",
                              monthAbbr[e->month], e->day, e->text);
  }
  String s;
  s += MARKER_HIST;
  s += " On this day: ";
  s += buf;
  return s;
}

// =================================================================
//                         DRAW THE FRAME
// =================================================================

void drawAnalogClock(const struct tm& t) {
  display.drawCircle(CX, CY, R, SSD1306_WHITE);

  for (int i = 0; i < 60; i++) {
    if (i % 5 == 0) continue;
    float a = (i * 6.0f - 90.0f) * DEG_TO_RAD;
    int16_t x = CX + (int16_t)lroundf((R - 2) * cosf(a));
    int16_t y = CY + (int16_t)lroundf((R - 2) * sinf(a));
    display.drawPixel(x, y, SSD1306_WHITE);
  }
  for (int i = 0; i < 12; i++) {
    float a  = (i * 30.0f - 90.0f) * DEG_TO_RAD;
    float cs = cosf(a), sn = sinf(a);
    int16_t x0 = CX + (int16_t)lroundf((R - 4) * cs);
    int16_t y0 = CY + (int16_t)lroundf((R - 4) * sn);
    int16_t x1 = CX + (int16_t)lroundf((R - 1) * cs);
    int16_t y1 = CY + (int16_t)lroundf((R - 1) * sn);
    display.drawLine(x0, y0, x1, y1, SSD1306_WHITE);
  }
  display.setTextColor(SSD1306_WHITE);
  for (int i = 1; i <= 12; i++) drawHourNumber(i, i * 30.0f, NUM_RAD);
  display.setFont();

  int hour   = t.tm_hour % 12;
  int minute = t.tm_min;
  int second = t.tm_sec;
  float hourAngle = hour * 30.0f + minute * 0.5f;
  float minAngle  = minute * 6.0f + second * 0.1f;
  float secAngle  = second * 6.0f;

  drawWedgeHand(hourAngle, HOUR_LEN, HOUR_BASE);
  drawWedgeHand(minAngle,  MIN_LEN,  MIN_BASE);

  int16_t sx, sy, tx, ty;
  polar(secAngle,          SEC_LEN, sx, sy);
  polar(secAngle + 180.0f, 4,       tx, ty);
  display.drawLine(tx, ty, sx, sy, SSD1306_WHITE);

  display.fillCircle(CX, CY, 2, SSD1306_WHITE);
  display.drawPixel(CX, CY, SSD1306_BLACK);

  int16_t bx, by;
  polar(secAngle, R, bx, by);
  display.fillCircle(bx, by, 1, SSD1306_WHITE);
}

void drawDigitalPanel(const struct tm& t) {
  display.setFont(); display.setTextSize(1); display.setTextColor(SSD1306_WHITE);

  char tzBuf[8];
  strftime(tzBuf, sizeof(tzBuf), "%Z", &t);
  if (tzBuf[0] == '\0') strcpy(tzBuf, "---");
  String title = String("CLOCK ") + tzBuf;
  int16_t x1, y1; uint16_t tw, th;
  display.getTextBounds(title, 0, 0, &x1, &y1, &tw, &th);
  const int16_t GAP = 3;
  int16_t blockW = (int16_t)tw + GAP + SIGNAL_ICON_W;
  int16_t blockX = TEXT_X_LEFT + (PANEL_W - blockW) / 2;
  if (blockX < TEXT_X_LEFT) blockX = TEXT_X_LEFT;
  display.setCursor(blockX, ROW_Y[0]);
  display.print(title);
  bool animate = (millis() < fetchAnimUntil);
  drawSignalIcon(blockX + tw + GAP - 2, ROW_Y[0], WiFi.RSSI(), animate);

  static const char* const days[] = {
    "Sunday", "Monday", "Tuesday", "Wednesday",
    "Thursday", "Friday", "Saturday"
  };
  drawCenteredInPanel(days[t.tm_wday], ROW_Y[1]);

  static const char* const months[] = {
    "Jan","Feb","Mar","Apr","May","Jun",
    "Jul","Aug","Sep","Oct","Nov","Dec"
  };
  char dateBuf[20];
  snprintf(dateBuf, sizeof(dateBuf), "%s %d %d",
           months[t.tm_mon], t.tm_mday, t.tm_year + 1900);
  drawCenteredInPanel(String(dateBuf), ROW_Y[2]);

  int hour12 = t.tm_hour % 12; if (hour12 == 0) hour12 = 12;
  char timeBuf[16];
  snprintf(timeBuf, sizeof(timeBuf), "%d:%02d:%02d %s",
           hour12, t.tm_min, t.tm_sec,
           t.tm_hour < 12 ? "AM" : "PM");
  drawCenteredInPanel(String(timeBuf), ROW_Y[3]);
}

void drawTicker() {
  if (!hasNews) return;
  const String& s = (tickerMode == TM_NEWS) ? newsText : cardText;
  drawScrollSegment(s, (int16_t)scrollX, NEWS_Y);
}

void drawFrame() {
  struct tm t;
  bool haveTime = getLocalTime(&t, 50);

  if (xSemaphoreTake(dataMutex, portMAX_DELAY) != pdTRUE) return;

  display.clearDisplay();
  if (haveTime) {
    drawAnalogClock(t);
    drawDigitalPanel(t);
  } else {
    display.setFont(); display.setTextSize(1); display.setTextColor(SSD1306_WHITE);
    display.setCursor(0, 20); display.print("Waiting for NTP...");
  }
  drawTicker();
  
  // Chenarul a fost eliminat (comentat)
  // drawBorder();

  if (millis() < newsFlashUntil)
    display.fillRect(6, 6, 3, 3, SSD1306_WHITE);

  display.display();
  xSemaphoreGive(dataMutex);
}

// =================================================================
//                   NETWORK TASK (core 0)
// =================================================================

void networkTask(void* pv) {
  for (;;) {
    unsigned long now = millis();
    if (WiFi.status() == WL_CONNECTED && now >= nextRssFetch) {
      bool ok = fetchNews();
      unsigned long interval = RSS_REFRESH_MIN * 60UL * 1000UL;
      nextRssFetch = millis() + (ok ? interval : 5UL * 60UL * 1000UL);
    }
    vTaskDelay(pdMS_TO_TICKS(200));
  }
}

// =================================================================
//                     TICKER STATE MACHINE
// =================================================================

// Build a card and enter CP_ENTER (or CP_LONG if too wide to fit).
void enterCardMode(unsigned long now) {
  struct tm tnow;
  String built;
  if (getLocalTime(&tnow, 10)) built = buildOnThisDay(tnow);
  if (built.length() == 0) {
    scrollX = SCREEN_WIDTH;       // no card available; loop news
    return;
  }
  tickerMode = TM_CARD;
  cardText   = built;
  cardTextW  = computeScrollWidth(cardText);
  // Card "fits" if it can be shown centered within the visible ticker area.
  cardFits   = (cardTextW <= SCREEN_WIDTH - 2 * TICKER_MARGIN);

  if (cardFits) {
    cardDwellX     = (SCREEN_WIDTH - (int16_t)cardTextW) / 2;
    cardPhase      = CP_ENTER;
    cardPhaseStart = now;
    scrollX        = SCREEN_WIDTH;   // slide in from right
  } else {
    cardPhase      = CP_LONG;
    cardPhaseStart = now;
    scrollX        = SCREEN_WIDTH;
  }
}

// Returns true when card is done and ticker should flip back to news.
bool updateCard(unsigned long now, float dt) {
  float cardSpeed = SCROLL_SPEED_PXS * CARD_SPEED_FACTOR;

  switch (cardPhase) {
    case CP_ENTER: {
      scrollX -= cardSpeed * dt;
      if (scrollX <= (float)cardDwellX) {
        scrollX        = (float)cardDwellX;
        cardPhase      = CP_DWELL;
        cardPhaseStart = now;
      }
      return false;
    }
    case CP_DWELL: {
      if (now - cardPhaseStart >= CARD_DWELL_MS) {
        cardPhase      = CP_EXIT;
        cardPhaseStart = now;
      }
      return false;
    }
    case CP_EXIT: {
      scrollX -= cardSpeed * dt;
      return (scrollX < -(float)cardTextW);
    }
    case CP_LONG: {
      scrollX -= cardSpeed * dt;
      if (scrollX < -(float)cardTextW) scrollX = SCREEN_WIDTH;  // loop
      if (now - cardPhaseStart >= CARD_DWELL_MS) {
        cardPhase      = CP_EXIT;     // finish current pass cleanly
        cardPhaseStart = now;
      }
      return false;
    }
  }
  return false;
}

// =================================================================
//                           SETUP / LOOP
// =================================================================

void setup() {
  Serial.begin(115200); delay(300);
  dataMutex = xSemaphoreCreateMutex();

  Wire.begin(SDA_PIN, SCL_PIN);
  if (!display.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR)) {
    Serial.println("OLED not found");
    while (true) delay(1000);
  }
  display.setTextWrap(false);
  display.setRotation(2); // Rotirea ta

  showMessage("Connecting WiFi", WIFI_SSID);
  WiFi.mode(WIFI_STA); WiFi.begin(WIFI_SSID, WIFI_PASS);
  WiFi.setTxPower(WIFI_POWER_8_5dBm); // decrease power for wifiz
  unsigned long start = millis();
  while (WiFi.status() != WL_CONNECTED && millis() - start < 20000) {
    delay(300); Serial.print(".");
  }
  if (WiFi.status() != WL_CONNECTED) {
    showMessage("WiFi FAILED", "Check credentials");
    while (true) delay(1000);
  }
  Serial.print("\nWiFi OK, IP: "); Serial.println(WiFi.localIP());
  showMessage("WiFi connected", WiFi.localIP().toString());
  delay(500);

  configTzTime(TIMEZONE, NTP_SERVER);
  showMessage("Syncing NTP...", NTP_SERVER);
  struct tm t;
  unsigned long ntpStart = millis();
  while (!getLocalTime(&t, 100) && millis() - ntpStart < 10000) delay(200);

  showMessage("Fetching news...", "(first run)");
  fetchNews();
  unsigned long interval = RSS_REFRESH_MIN * 60UL * 1000UL;
  nextRssFetch = millis() + (hasNews ? interval : 5UL * 60UL * 1000UL);

  lastScrollTick = millis();
  lastFrame      = 0;
  scrollX        = SCREEN_WIDTH;
  tickerMode     = TM_NEWS;

  xTaskCreatePinnedToCore(networkTask, "netTask", 16384, NULL, 1, NULL, 0);
}

void loop() {
  static unsigned long lastWifiCheck = 0;
  unsigned long now = millis();

  if (now - lastWifiCheck > 30000) {
    lastWifiCheck = now;
    if (WiFi.status() != WL_CONNECTED) WiFi.reconnect();
  }

  if (hasNews) {
    float dt = (now - lastScrollTick) / 1000.0f;

    if (tickerMode == TM_NEWS) {
      scrollX -= SCROLL_SPEED_PXS * dt;
      if (scrollX < -(float)newsTextW) {
        enterCardMode(now);
      }
    } else {
      if (updateCard(now, dt)) {
        tickerMode = TM_NEWS;
        scrollX    = SCREEN_WIDTH;
      }
    }
  }
  lastScrollTick = now;

  if (now - lastFrame >= SCROLL_FRAME_MS) {
    lastFrame = now;
    drawFrame();
  }
}
