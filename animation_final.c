/**
 * Hunter Adams (vha3@cornell.edu)
 * 
 * This demonstration animates two balls bouncing about the screen.
 * Through a serial interface, the user can change the ball color.
 *
 * HARDWARE CONNECTIONS
  - GPIO 16 ---> VGA Hsync
  - GPIO 17 ---> VGA Vsync
  - GPIO 18 ---> VGA Green lo-bit --> 470 ohm resistor --> VGA_Green
  - GPIO 19 ---> VGA Green hi_bit --> 330 ohm resistor --> VGA_Green
  - GPIO 20 ---> 330 ohm resistor ---> VGA-Blue
  - GPIO 21 ---> 330 ohm resistor ---> VGA-Red
  - RP2040 GND ---> VGA-GND
 *
 * RESOURCES USED
 *  - PIO state machines 0, 1, and 2 on PIO instance 0
 *  - DMA channels (2, by claim mechanism)
 *  - 153.6 kBytes of RAM (for pixel color data)
 *
 */

// Include the VGA graphics library
#include "vga16_graphics_v2.h"
// Include standard libraries 
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <time.h>

// Include Pico libraries
#include "pico/stdlib.h"
#include "pico/divider.h"
#include "pico/multicore.h"
// Include hardware libraries
#include "hardware/pio.h"
#include "hardware/dma.h"
#include "hardware/clocks.h"
#include "hardware/pll.h"
#include "hardware/spi.h"
#include "hardware/regs/dreq.h"
#include "hardware/adc.h"
// Include protothreads
#include "pt_cornell_rp2040_v1_4.h"

// === the fixed point macros ========================================
typedef signed int fix15 ;
#define multfix15(a,b) ((fix15)((((signed long long)(a))*((signed long long)(b)))>>15))
#define float2fix15(a) ((fix15)((a)*32768.0)) // 2^15
#define fix2float15(a) ((float)(a)/32768.0)
#define absfix15(a) abs(a) 
#define int2fix15(a) ((fix15)(a << 15))
#define fix2int15(a) ((int)(a >> 15))
#define char2fix15(a) (fix15)(((fix15)(a)) << 15)
#define divfix(a,b) (fix15)(div_s64s64( (((signed long long)(a)) << 15), ((signed long long)(b))))
#define sqrtfix(a) (float2fix(sqrt(fix2float(a))))

static inline fix15 sqrtfix15(fix15 a){
  return float2fix15(sqrtf(fix2float15(a)));
}

#define MAX_PEGS 136  // for 16-row
#define MAX_BALLS 4000
#define NUM_BINS 17
#define BUTTON_PIN 15
#define LED_PIN 25  // The LED is connected to GPIO 25

typedef struct {
  fix15 x;
  fix15 y;
} Peg;
Peg pegs[MAX_PEGS];

typedef struct {
  fix15 x;
  fix15 y;
  fix15 vx;
  fix15 vy;
} Ball;
Ball balls[MAX_BALLS];

// peg and ball radius
const int peg_radius_px = 6;
const int ball_radius_px = 1;

static int peg_count = 0;
static int num_balls;

// HUD / counters
static volatile uint32_t total_fallen = 0;   
static int prev_num_balls = 0;  

// histogram globals
int bins[NUM_BINS] = {0};
const int bin_width_px = 640 / NUM_BINS;
volatile int hist_needs_clear = 0;

// Wall detection
#define hitBottom(b) (b>int2fix15(335))
#define hitTop(b) (b<int2fix15(0))
#define hitLeft(a) (a<int2fix15(0))
#define hitRight(a) (a>int2fix15(640))

// uS per frame
#define FRAME_RATE 33000

#define VGA_RATE 200000
static int vga_display = 0;

static uint32_t fps_current  = 30;

// the color of the boid
char color = WHITE ;

volatile int sound = 1;

// Boid on core 0
fix15 boid0_x ;
fix15 boid0_y ;
fix15 boid0_vx ;
fix15 boid0_vy ;

const fix15 GRAVITY = float2fix15(0.75f);
volatile fix15 bounciness;
static fix15 bounciness_target= float2fix15(0.5f);

// DMA
// Number of samples per period in sine table
#define sine_table_size 256

// Sine table
int raw_sin[sine_table_size] ;

// Table of values to be sent to DAC
unsigned short DAC_data[sine_table_size] ;

// Pointer to the address of the DAC data table
unsigned short * dma_address_pointer = &DAC_data[0] ;

// A-channel, 1x, active
#define DAC_config_chan_A 0b0011000000000000

//SPI configurations
#define PIN_MISO 4
#define PIN_CS   5
#define PIN_SCK  6
#define PIN_MOSI 7
#define SPI_PORT spi0

// Number of DMA transfers per event
const uint32_t transfer_count = sine_table_size ;

int data_chan ;
int ctrl_chan ;

// button fsm states 
#define STATE_RESET 0
#define STATE_BALLS 1
#define STATE_BOUNCE 2

volatile int state = STATE_RESET;

static uint32_t adc_filtered = 0;

// ==================================================
// === peg pyramid initialization function
// ==================================================
void initPeg(fix15 px, fix15 py, fix15 rows) {
  int x = px;
  int y = py;
  int startx = x;
  int starty = y;

  int peg_array_count = 0;
  for (int i=1; i<=rows; i++) {
    if (i==1) {
      pegs[peg_array_count].x = int2fix15(x);
      pegs[peg_array_count].y = int2fix15(y);
      peg_array_count++;
    } else {
      int peg_count = i;
      startx = startx - 19;
      starty = starty + 19;
      for (int n=peg_count; n>0; n--) {
        pegs[peg_array_count].x = int2fix15(startx + (n-1)*38);
        pegs[peg_array_count].y = int2fix15(starty);
        peg_array_count++;
      }
    }
  }
  peg_count = peg_array_count;
}

// ==================================================
// === peg drawing function
// ==================================================
void drawPeg() {
  for (int i = 0; i < peg_count; i++) {
    int x = fix2int15(pegs[i].x);
    int y = fix2int15(pegs[i].y);
    drawCircle(x, y, peg_radius_px, PINK);
  }
}

// ==================================================
// === histogram drawing thread 
// ==================================================
static PT_THREAD(protothread_histogram(struct pt *pt))
{
  PT_BEGIN(pt);

  // private "previous heights" so incremental updates work
  static int prev_bin_heights[NUM_BINS];
  for (int i = 0; i < NUM_BINS; i++) prev_bin_heights[i] = 0;

  // pick an update cadence (200 ms = 5 Hz)
  const int HIST_PERIOD_US = 200000;

  while (1) {
    // --- compute histogram drawing region based on pegs ---
    int peg_bottom_y = (peg_count > 0) ? (fix2int15(pegs[peg_count-1].y) + 2*peg_radius_px) : 100;
    int hist_top     = peg_bottom_y + 12;
    if (hist_top < 0) hist_top = 0;
    if (hist_top >= 480) hist_top = 480 - 1;
    int hist_height  = 480 - hist_top - 2;
    if (hist_height < 8) hist_height = 8;

    // --- if anim changed parameters, clear bins & screen area ---
    if (hist_needs_clear) {
      // clear the on-screen histogram strip
      fillRect(0, hist_top, 640, hist_height, BLACK);

      // reset data & incremental state
      total_fallen = 0;
      for (int i = 0; i < NUM_BINS; i++) {
        ((volatile int*)bins)[i] = 0;   // cast quiets some compilers
        prev_bin_heights[i] = 0;
      }
      hist_needs_clear = 0;
    }

    // --- incremental update exactly like your old update_histogram() ---
    // find max count for normalization (avoid div-by-zero)
    int max_bin_count = 1;
    for (int i = 0; i < NUM_BINS; ++i) {
      int v = bins[i];
      if (v > max_bin_count) max_bin_count = v;
    }

    for (int i = 0; i < NUM_BINS; ++i) {
      int x0 = i * bin_width_px;
      int w  = (i == NUM_BINS - 1) ? (640 - x0) : (bin_width_px - 1);

      int new_h = (bins[i] * hist_height) / max_bin_count;
      if (bins[i] > 0 && new_h == 0) new_h = 1; // show tiny bar when non-zero

      int old_h = prev_bin_heights[i];

      if (new_h > old_h) {
        int top_of_new  = hist_top + (hist_height - new_h);
        int grow_pixels = new_h - old_h;
        if (grow_pixels > 0) {
          int y_add = top_of_new;
          fillRect(x0, y_add, w, grow_pixels, PINK);
        }
      } else if (new_h < old_h) {
        int top_of_old   = hist_top + (hist_height - old_h);
        int erase_pixels = old_h - new_h;
        if (erase_pixels > 0) {
          int y_erase = top_of_old;
          fillRect(x0, y_erase, w, erase_pixels, BLACK);
        }
      }
      prev_bin_heights[i] = new_h;
    }

    // run at fixed cadence; the rest of the system is cooperative
    PT_YIELD_usec(HIST_PERIOD_US);
  }

  PT_END(pt);
}

// ==================================================
// === collisions, edges, and respawn logic function
// ==================================================
void wallsAndEdges(Ball* b) {
  for (int i = 0; i < MAX_PEGS ; i++) {
    // Compute x and y distances between ball and peg
    fix15 dx = b->x - pegs[i].x;
    fix15 dy = b->y - pegs[i].y;

    fix15 collision_dist = int2fix15(ball_radius_px + peg_radius_px);
    
    // Are both the x and y distances less than the collision distance?
    if (absfix15(dx) < collision_dist && absfix15(dy) < collision_dist) {
      // alpha beta algorithm for sqrt()
      fix15 ax = (dx < 0) ? -dx : dx;
      fix15 ay = (dy < 0) ? -dy : dy;
      fix15 max_v = (ax > ay) ? ax : ay;
      fix15 min_v = (ax > ay) ? ay : ax;
      fix15 distance = max_v + (min_v >> 2);

      if (distance == 0) continue; // to avoid dividing by zero

      // Generate the normal vector that points from peg to ball
      fix15 normal_x = divfix(dx, distance);
      fix15 normal_y = divfix(dy, distance);
      
      // Collision physics
      fix15 intermediate_term = -((multfix15(normal_x, b->vx) + multfix15(normal_y, b->vy)) << 1)  ; // Shift by 1
      // Are the ball velocity and normal vectors in opposite directions?
      if (intermediate_term > 0){
        
        // Teleport it outside the collision distance with the peg
        b->x = pegs[i].x + multfix15(normal_x, distance + 1);
        b->y = pegs[i].y + multfix15(normal_y, distance + 1);
        // Update its velocity
        b->vx = b->vx + multfix15(normal_x, intermediate_term);
        b->vy = b->vy + multfix15(normal_y , intermediate_term);

        b->vx = multfix15(bounciness , b->vx);
        b->vy = multfix15(bounciness , b->vy);

        // add sound 
        sound = 1;
      }
    }
    
  }

  // Reverse direction if we've hit a wall
    if (hitTop(b->y)) {
      b->vy = (-b->vy) ;
      b->y  = (b->y + int2fix15(5)) ;
    }
    // Re-spawn any balls that fall thru bottom
    if (hitBottom(b->y)) {
      total_fallen++;  

      int x_px = fix2int15(b->x);

      if (x_px < 0) x_px = 0;
      if (x_px >= 640) x_px = 640 - 1;

      // creates x position to histogram bin index
      int bin_index = (x_px * NUM_BINS) / 640; 
      if (bin_index >= 0 && bin_index < NUM_BINS) {
          bins[bin_index]++;
      }
      b->y  = int2fix15(30) ; 
      b->vy = (0) ;
      b->x = int2fix15(320) ;
      b->vx = (fix15)(rand() >> 16) - 16384;
    } 

    if (hitRight(b->x)) {
      b->vx = (-b->vx) ;
      b->x  = (b->x - int2fix15(5)) ;
    }
    if (hitLeft(b->x)) {
      b->vx = (-b->vx) ;
      b->x  = (b->x + int2fix15(5)) ;
    } 
    
    // apply gravity
    b->vy = b->vy + GRAVITY;

    // Update position using velocity
    b->x = b->x + b->vx ;
    b->y = b->y + b->vy ;
}

// ==================================================
// === core 0 animation thread
// ==================================================
static PT_THREAD (protothread_anim(struct pt *pt)) 
{
  // Mark beginning of thread
  PT_BEGIN(pt);

  // Variables for maintaining frame rate
  static int begin_time ;
  static int spare_time ;

  while(1) {
    // Measure time at start of thread
    begin_time = time_us_32() ;    
    bool vga_due= (begin_time - vga_display) >= 0;
    if (vga_due){
      vga_display = begin_time + VGA_RATE;
    }
    // draw peg
    drawPeg();
    
    int new_num_balls = num_balls;
    fix15 prev_bounce_target = bounciness_target;
    
    if (state == STATE_RESET) {
      new_num_balls = MAX_BALLS;
      bounciness_target = float2fix15(0.5f);
    }
    else if (state == STATE_BALLS) {
      new_num_balls = (adc_filtered * MAX_BALLS) / 4095;
    }
    else if (state == STATE_BOUNCE) {
      bounciness_target = float2fix15(adc_filtered/ 4095.0f);
    }
    
    // decide if a histogram reset is needed (threshold same as before)
    if ((abs(num_balls - new_num_balls) > 2) ||
        (absfix15(bounciness - bounciness_target) > float2fix15(0.003f))) {
      hist_needs_clear = 1;     // histogram thread will do the clear
    }

    // update bounciness
    bounciness = bounciness_target;
    
    // clamp new_num_balls
    if (new_num_balls < 0) {
      new_num_balls = 0;
    }
    if (new_num_balls > MAX_BALLS) {
      new_num_balls = MAX_BALLS;
    }

    if (new_num_balls > num_balls) {
      for (int i = num_balls; i < new_num_balls; i++) {
        if (i >= MAX_BALLS) break;
        balls[i].x  = int2fix15(640/2);
        balls[i].y  = int2fix15(35);
        balls[i].vy = int2fix15(0);
        balls[i].vx = (fix15)((rand() & 0x7FFF) - 0x4000); 
      }
    }

    // update number of balls
    num_balls = new_num_balls;

    //if amount of balls decrease, erase leftover balls
    if (prev_num_balls > num_balls) {
      for (int i = num_balls; i < prev_num_balls; i++) {
        fillCircle(fix2int15(balls[i].x), fix2int15(balls[i].y), ball_radius_px + 1, BLACK);
      }
    }

    for(int i = 0; i < num_balls; i++) {
      // // erase boid
      drawCircle(fix2int15(balls[i].x), fix2int15(balls[i].y), ball_radius_px, BLACK);
      fillCircle(fix2int15(balls[i].x), fix2int15(balls[i].y), ball_radius_px, BLACK);
      // update boid's position and velocity
      wallsAndEdges(&balls[i]) ;
      // draw the boid at its new position
      drawCircle(fix2int15(balls[i].x), fix2int15(balls[i].y), ball_radius_px, color); 
    }
    prev_num_balls = num_balls;

    uint32_t work_us = time_us_32() - begin_time;
    if (work_us == 0) {
      work_us = 1;
    }
    fps_current = (1000000u + (work_us >> 1)) / work_us;  // natural FPS
    
    uint16_t result = adc_read();
    adc_filtered = (adc_filtered*7 + result) >> 3;

    // delay in accordance with frame rate
    spare_time = FRAME_RATE - (time_us_32() - begin_time) ;
    if (spare_time <= 0) spare_time = 1;

    // yield for necessary amount of time
    PT_YIELD_usec(spare_time) ;
    // NEVER exit while
  } // END WHILE(1)

  PT_END(pt);
} // animation thread


// ==================================================
// === dma sound function
// ==================================================
static inline void dma_play_sine_once(void) {
  dma_channel_wait_for_finish_blocking(data_chan);
  dma_channel_set_read_addr(data_chan, DAC_data, false);
  dma_channel_set_trans_count(data_chan, sine_table_size, true);
}

// ==================================================
// === collision thunk sound thread
// ==================================================
static PT_THREAD(protothread_beep(struct pt *pt))
{
  PT_BEGIN(pt);
  
  while (sound) {
    dma_play_sine_once();
    sound = 0;
  }

  PT_END(pt);
}

// ==================================================
// === mode button thread
// ==================================================
static PT_THREAD(protothread_button(struct pt *pt))
{
  PT_BEGIN(pt);
  
  gpio_init(BUTTON_PIN);
  gpio_set_dir(BUTTON_PIN, GPIO_IN);
  gpio_pull_up(BUTTON_PIN);

  static bool prev = true;  // not pressed
  while (1) {
    bool now = gpio_get(BUTTON_PIN);
    if (prev && !now) {
      if (state == STATE_RESET) {
        state = STATE_BALLS;
      }
      else if (state == STATE_BALLS) {
        state = STATE_BOUNCE;
      }
      else if (state == STATE_BOUNCE) {
        state = STATE_BALLS;
      }
    }
    prev = now;
    PT_YIELD_usec(1000);  // debounce
  }

  PT_END(pt);
}

// ==================================================
// === fps LED thread
// ==================================================
static PT_THREAD(protothread_led(struct pt *pt))
{
  PT_BEGIN(pt);

  // Initialize the LED pin
  gpio_init(LED_PIN);
  // Configure the LED pin as an output
  gpio_set_dir(LED_PIN, GPIO_OUT);
  
  while (1) {
    if (fps_current < 30) {
      // set high
      gpio_put(LED_PIN, 1);
    } else {
      // set low
      gpio_put(LED_PIN, 0);
    }
    PT_YIELD_usec(1000);
  }
  
  PT_END(pt);
}

// ==================================================
// === HUD text thread
// ==================================================
static PT_THREAD(protothread_hud(struct pt *pt))
{
  PT_BEGIN(pt);

  // text area
  const int hud_x = 12;
  const int hud_y = 12;
  const int hud_w = 260;
  const int hud_h = 72;

  setTextColor(WHITE);
  setTextColor2(WHITE, BLACK);
  setTextSize(1);
  setTextWrap(0);

  while (1) {
    // clear HUD rectangle each frame
    fillRect(hud_x, hud_y, hud_w, hud_h, BLACK);

    char buf[64];

    // Line 1: Mode
    setCursor(20, 20);
    if (state == STATE_RESET) {
      sprintf(buf, "Mode: None");
    }
    else if (state == STATE_BALLS) {
      sprintf(buf, "Mode: Ball Number");
    }
    else if (state == STATE_BOUNCE) {
      sprintf(buf, "Mode: Bounciness");
    }
    else {
      sprintf(buf, "Mode: ?");
    }
    writeString(buf);

    // Line 2: Balls
    setCursor(20, 30);
    sprintf(buf, "Balls: %d", num_balls);
    writeString(buf);

    // Line 3: Fallen
    setCursor(20, 40);
    sprintf(buf, "Balls Fallen: %u", total_fallen);
    writeString(buf);

    // Line 4: Bounciness
    setCursor(20, 50);
    sprintf(buf, "Bounciness: %.2f", fix2float15(bounciness));
    writeString(buf);

    // Line 5: Runtime
    unsigned int runtime_ms = time_us_32() / 1000;
    unsigned int sec = (runtime_ms / 1000) % 60;
    unsigned int min =  runtime_ms / 60000;
    setCursor(20, 60);
    sprintf(buf, "Runtime: %02u:%02u", min, sec);
    writeString(buf);

    // Line 6: FPS
    setCursor(20, 70);
    sprintf(buf, "FPS: %-3u", fps_current);
    writeString(buf);

    // yield longer to update 5 times a second
    PT_YIELD_usec(200000);
  }

  PT_END(pt);
}

// ========================================
// === main
// ========================================
// USE ONLY C-sdk library
int main()
{
  set_sys_clock_khz(250000, true) ;
  // initialize stio
  stdio_init_all() ;
  adc_init();
  // Make sure GPIO is high-impedance, no pullups etc
  adc_gpio_init(26);
  // Select ADC input 0 (GPIO26)
  adc_select_input(0);
  srand(time_us_32());
  // initialize VGA
  initVGA();
  setTextColor(WHITE);        // set the ink color the font code reads
  setTextColor2(WHITE, BLACK); // (ok to keep; sets bg as well)
  setTextSize(1);
  setTextWrap(0);

  // Initialize SPI channel (channel, baud rate set to 20MHz)
  spi_init(SPI_PORT, 20000000) ;

  // Format SPI channel (channel, data bits per transfer, polarity, phase, order)
  spi_set_format(SPI_PORT, 16, 0, 0, 0);
  
  // Map SPI signals to GPIO ports, acts like framed SPI with this CS mapping
  gpio_set_function(PIN_MISO, GPIO_FUNC_SPI);
  gpio_set_function(PIN_CS, GPIO_FUNC_SPI) ;
  gpio_set_function(PIN_SCK, GPIO_FUNC_SPI);
  gpio_set_function(PIN_MOSI, GPIO_FUNC_SPI);

  // Build sine table and DAC data table
  int i ;
  for (i=0; i<(sine_table_size); i++) {
      raw_sin[i] = (int)(2047 * sin((float)i*6.283/(float)sine_table_size) + 2047); //12 bit
      DAC_data[i] = DAC_config_chan_A | (raw_sin[i] & 0x0fff) ;
  }

  // Initialize array of peg positions
  initPeg(320, 50, 16); 

  // Select DMA channels
  data_chan = dma_claim_unused_channel(true);

  // Setup the data channel
  dma_channel_config c2 = dma_channel_get_default_config(data_chan);  // Default configs
  channel_config_set_transfer_data_size(&c2, DMA_SIZE_16);            // 16-bit txfers
  channel_config_set_read_increment(&c2, true);                       // yes read incrementing
  channel_config_set_write_increment(&c2, false);                     // no write incrementing
  // (X/Y)*sys_clk, where X is the first 16 bytes and Y is the second
  // sys_clk is 125 MHz unless changed in code. Configured to ~44 kHz
  dma_timer_set_fraction(0, 0x0017, 0xffff) ;
  // 0x3b means timer0 (see SDK manual)
  channel_config_set_dreq(&c2, 0x3b);                                 // DREQ paced by timer 0

  dma_channel_configure(
      data_chan,                  // Channel to be configured
      &c2,                        // The configuration we just created
      &spi_get_hw(SPI_PORT)->dr,  // write address (SPI data register)
      DAC_data,                   // The initial read address
      sine_table_size,            // Number of transfers
      false                       // Don't start immediately.
  );

  // add threads
  pt_add_thread(protothread_serial);
  pt_add_thread(protothread_beep);
  pt_add_thread(protothread_anim);
  pt_add_thread(protothread_button);
  pt_add_thread(protothread_led);
  pt_add_thread(protothread_histogram);
  pt_add_thread(protothread_hud);
  // start scheduler
  pt_schedule_start;

}