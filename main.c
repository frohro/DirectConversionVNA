/******************************************************************************
 * 2016 WWU Direct Conversion VNA
 * Author: Rob Frohne
 * Thanks to Gerard Sequeira, 43oh for the backchannel UART ideas and to TI for
 * the examples and driverlib.
*******************************************************************************/

#define USE_SPI
/* DriverLib Includes */
#include "driverlib.h"
#include "msp432.h"
#include "hw_memmap.h"

/* Standard Includes */
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

#include <string.h>
#include "printf.h"
#include <math.h>


/* Globals */

/* I2C constants */
#define SLAVE_ADDRESS       0x06a // Primary address 0x6a works for 0xd4
#define NUM_OF_REG_BYTES 0x6a-0x10
#define NUM_OF_CHANGED_REG_BYTES 10
#define NUM_BANDS 25
#define NUM_BAND_BLOCKS 4
#define FIRST_REG 0x10
/* UART constants */
#define REFLECTION_MODE 0
#define TRANSMISSION_MODE 1
#define DDS_RATIO 10737.41824 /* The tuning word conversion for the miniVNA that uses
						a 400MHz 32 bit DDS.  We need to divide by this to
						get what the frequency the miniVNA is trying to tell
						us. */
/* ADC14 constants */
#define NUM_ADC14_CHANNELS 4
#define VREF ADC_VREFPOS_AVCC_VREFNEG_VSS
/* Other constants */
#define PI atan(1.0)
#define TO_DEGREES 180/PI

const uint8_t firstReg = FIRST_REG;
static uint8_t TXByteCtr;
static uint8_t i2cRXData[NUM_OF_REG_BYTES+0x10];
const static volatile uint8_t *TXData;
static volatile uint32_t xferIndex;
static volatile bool justSending;

/* Initial data structure for I2C parameters.
 * We will only change the parameters that need changed.
 */
const struct VersaClockRegisters { /* VersaClock Register Data
	 * We first initialize registers for 1MHz operation.
	 * Then when we change frequencies, we change only the
	 * registers that change when frequencies change.
	 * These registers come in four blocks. The first block is 2 long;
	 * the second is 1; the third block is 2 long, and the last is 5 long. */
	uint8_t blockNumBytes[NUM_BAND_BLOCKS];
	uint8_t blockFirstAddress[NUM_BAND_BLOCKS];
	uint8_t changedAddresses[NUM_OF_CHANGED_REG_BYTES];
	/* The band edges:  The index of the frequency of the lower edge
	 * goes with the same index of the registers to send for that band. */
	long int frequencyBandLimit[NUM_BANDS+1];
	/* The register values for each of the 24 bands. */
	uint8_t registerValues[NUM_BANDS][NUM_OF_CHANGED_REG_BYTES];
	/* The init1MHzRegisterValues are for the 1 MHz to 1.199 MHz band. */
	uint8_t init1MHzRegisterValues[NUM_OF_REG_BYTES];
} versaClockRegisters =
		{{2,1,2,5},
		{0x17,0x1e,0x2d,0x3b},
		{0x17,0x18,0x1e,0x2d,0x2e,0x3b,0x3c,0x3d,0x3e,0x3f},
		{1000,1199,1438,1726,2068,2479,2970,3562,4273,5119,6122,7317,8771,10489,
		12500,15000,17857,21126,25000,30000,35714,41666,48387,57692,68181,70001},
		{{0x9c,0x40,0x50,0x4e,0x20,0x61,0xa0,0x4e,0x20,0x20},
		 {0x82,0x40,0x60,0x41,0x20,0x51,0x60,0x41,0x20,0x20},
		 {0x6c,0xa0,0x70,0x36,0x50,0x0d,0x90,0x36,0x50,0x10},
		 {0x5a,0xa0,0x80,0x2d,0x50,0x0b,0x50,0x2d,0x50,0x10},
		 {0x4b,0xa0,0x88,0x25,0xd0,0x09,0x70,0x25,0xd0,0x10},
		 {0x3f,0x20,0x90,0x1f,0x90,0x07,0xe0,0x1f,0x90,0x10},
		 {0x34,0xa0,0xa0,0x1a,0x50,0x06,0x90,0x1a,0x50,0x10},
		 {0x2b,0xe0,0xa9,0x15,0xf0,0x0b,0x60,0x15,0xf0,0x30},
		 {0x24,0xa0,0xb0,0x12,0x50,0x04,0x90,0x12,0x50,0x10},
		 {0x1e,0xa0,0xb8,0x0f,0x50,0x03,0xd0,0x0f,0x50,0x10},
		 {0x19,0xa0,0xb8,0x0c,0xd0,0x03,0x30,0x0c,0xd0,0x10},
		 {0x15,0x60,0xc0,0x0a,0xb0,0x0d,0x50,0x0a,0xb0,0x30},
		 {0x11,0xe0,0xc8,0x08,0xf0,0x0b,0x20,0x08,0xf0,0x30},
		 {0x1f,0x00,0xd0,0x07,0x80,0x01,0xe0,0x07,0x80,0x00},
		 {0x0c,0x80,0xd0,0x06,0x40,0x01,0x90,0x06,0x40,0x00},
		 {0x0a,0x80,0xd8,0x05,0x40,0x01,0x50,0x05,0x40,0x00},
		 {0x08,0xe0,0xd8,0x04,0x70,0x05,0x80,0x04,0x70,0x30},
		 {0x07,0x80,0xe0,0x03,0xc0,0x00,0xf0,0x03,0xc0,0x00},
		 {0x06,0x40,0xe0,0x03,0x20,0x03,0xe0,0x03,0x20,0x20},
		 {0x05,0x40,0xe0,0x02,0xa0,0x03,0x40,0x02,0xa0,0x20},
		 {0x04,0x80,0xe8,0x02,0x40,0x00,0x90,0x02,0x40,0x00},
		 {0x03,0xe0,0xe8,0x01,0xf0,0x02,0x60,0x01,0xf0,0x30},
		 {0x03,0x40,0xe8,0x01,0xa0,0x02,0x00,0x01,0xa0,0x20},
		 {0x02,0xc0,0xf0,0x01,0x60,0x01,0xb0,0x01,0x60,0x20},
		 {0x02,0x60,0xf0,0x01,0x30,0x01,0x70,0x01,0x30,0x30}},
		{0x40,0x0C,0x81,0x80,0x0,0x3,0x8C,
		 0x9C,0x40,0x0,0x0,0x0,0x9F,0xFF,0x50,0x80,0x0,0x81,
		 0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4,0x0,0x0,0x4E,0x20,
		 0x0,0x0,0x81,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4,0x61,
		 0xA0,0x4E,0x20,0x20,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,
		 0x0,0x0,0x4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,
		 0x0,0x0,0x0,0x0,0x0,0x4,0x0,0x0,0x0,0x0,0x0,0x3B,
		 0x1,0x3B,0x1,0x3B,0x0,0x3B,0x0,0xFF,0x64}};

/* I2C Master Configuration Parameter */
const eUSCI_I2C_MasterConfig i2cConfig =
{
        EUSCI_B_I2C_CLOCKSOURCE_SMCLK,          // SMCLK Clock Source
        3000000,                                // SMCLK = 3MHz
        EUSCI_B_I2C_SET_DATA_RATE_100KBPS,      // Desired I2C Clock of 100khz
        0,                                      // No byte counter threshold
        EUSCI_B_I2C_NO_AUTO_STOP                // No Autostop
};
/* I2C Master Configuration Parameter */

/* Results buffer for ADC14 */
uint16_t resultsBuffer[NUM_ADC14_CHANNELS]={0,0,0,0}; //ADC results

/* UART Configuration Parameter. These are the configuration parameters to
 * make the eUSCI A UART module to operate with a 115200 baud rate. These
 * values were calculated using the online calculator that TI provides
 * at:
 * http://processors.wiki.ti.com/index.php/
 *               USCI_UART_Baud_Rate_Gen_Mode_Selection
 *
 * On Linux use /dev/ttyACM0, 115200, 8N1.
 *               CuteCom works well.
 */
const eUSCI_UART_Config uartConfig =
{
        EUSCI_A_UART_CLOCKSOURCE_SMCLK,          // SMCLK Clock Source
        26,                                      // BRDIV = 26
        0,                                       // UCxBRF = 0
        0,                                       // UCxBRS = 0
        EUSCI_A_UART_NO_PARITY,                  // No Parity
        EUSCI_A_UART_LSB_FIRST,                  // MSB First
        EUSCI_A_UART_ONE_STOP_BIT,               // One stop bit
        EUSCI_A_UART_MODE,                       // UART mode
        EUSCI_A_UART_LOW_FREQUENCY_BAUDRATE_GENERATION  // Low Frequency Mode
};
char uartRXData[80];
static bool uartEndOfLineFlag = false;

#ifdef USE_SPI
/* SPI Master Configuration Parameter */
const eUSCI_SPI_MasterConfig spiMasterConfig =
{
		EUSCI_B_SPI_CLOCKSOURCE_SMCLK,
		// SMCLK Clock Source
		3000000,
		// SMCLK = DCO = 3MHZ
		500000,
		// SPICLK = 500khz
		EUSCI_B_SPI_LSB_FIRST,
		// MSB First
		EUSCI_B_SPI_PHASE_DATA_CHANGED_ONFIRST_CAPTURED_ON_NEXT,
		// Phase
		EUSCI_B_SPI_CLOCKPOLARITY_INACTIVITY_LOW, // Low polarity
		EUSCI_B_SPI_3PIN
		// 3Wire SPI Mode
};
#endif

/* Forward Declaration of Functions */
void initializeClocks(void);
int initializeBackChannelUART(void);
int initializeADC(void);
int initializeDDS(void);
int initializeVersaclock(void);
int initializeI2C(void);
int updateVersaclockRegs(long int frequency);
void dumpI2C(void);
void initVersaClock1MHz(void);
void writeVersaClockBlock(const uint8_t *firstDataPtr ,uint8_t blockStart, uint8_t numBytes);
int setDDSFrequency(long long frequency);
void pulseFQ_UD(void);
void pulse_W_CLK(void);
void pulse_DDS_RST(void);
void initI2C(void);
void reflectionMeasure(int fMin,int fMax,int numPts);
void transmissionMeasure(int fMin,int fMax,int numPts);


/*
 * USCIA0 interrupt handler for backchannel UART.
 * For interrupts, don't forget to edit the startup...c file!
 */
void EusciA0_ISR(void)
{
    //int receiveByte = UCA0RXBUF;
    static int i=0;
	uint32_t status = UART_getEnabledInterruptStatus(EUSCI_A0_BASE);

    UART_clearInterruptFlag(EUSCI_A0_BASE, status);

    if(status & EUSCI_A_UART_RECEIVE_INTERRUPT)
    {
        uartRXData[i] = UART_receiveData(EUSCI_A0_BASE);
        if(uartRXData[i++]==0x0d)
        {
        	uartEndOfLineFlag = true;
        	uartRXData[i] = 0;  // To end the array.
        }
    	//MAP_UART_transmitData(EUSCI_A0_BASE, UART_receiveData(EUSCI_A0_BASE));
    }
    else if(status & EUSCI_A_UART_TRANSMIT_INTERRUPT)
    {
    	/* Not sure we need this. */
    }
    /* Echo back. */
   // MAP_UART_transmitData(EUSCI_A0_BASE, receiveByte);
}

/*
 * This interrupt is fired whenever a conversion is completed and placed in
 * ADC_MEM7. This signals the end of conversion and the results array is
 * grabbed and placed in resultsBuffer
 */
void ADC14_IRQHandler(void)
{
    uint64_t status;
    status = ADC14_getEnabledInterruptStatus();
    ADC14_clearInterruptFlag(status);

    if(status & ADC_INT3)
    {
        ADC14_getMultiSequenceResult(resultsBuffer);
    }
}

/*
 * eUSCIB0 ISR.
 * For interrupts, don't forget to edit the startup...c file!
 */
void EUSCIB1_IRQHandler(void)
{
	uint_fast16_t status;

	status = I2C_getEnabledInterruptStatus(EUSCI_B1_BASE);
	I2C_clearInterruptFlag(EUSCI_B1_BASE, status);

	if(justSending) /* We don't need to worry about receiving. */
	{
		if (status & EUSCI_B_I2C_NAK_INTERRUPT)
		{
	        I2C_masterSendStart(EUSCI_B1_BASE);
		}

		if (status & EUSCI_B_I2C_TRANSMIT_INTERRUPT0)
		{
			/* Check the byte counter */
			if (TXByteCtr)
			{
				/* Send the next data and decrement the byte counter */
				I2C_masterSendMultiByteNext(EUSCI_B1_BASE, TXData[xferIndex++]);
				TXByteCtr--;
			} else
			{
				I2C_masterSendMultiByteStop(EUSCI_B1_BASE);
				xferIndex=0;
				Interrupt_disableSleepOnIsrExit();
			}
			//MAP_I2C_clearInterruptFlag(EUSCI_B1_BASE, status);
		}
	}
	else /* Not just sending.  We are reading the versaClock registers. */
	{
		/* If we reached the transmit interrupt, it means we are at the last byte (was index 1) of
		 * the transmit buffer. When doing a repeated start, before we reach the
		 * last byte we will need to change the mode to receive mode, set the start
		 * condition send bit, and then load the final byte into the TXBUF.
		 */
		if (status & EUSCI_B_I2C_TRANSMIT_INTERRUPT0)
		{
			//I2C_masterSendMultiByteNext(EUSCI_B1_BASE, firstReg);
			I2C_disableInterrupt(EUSCI_B1_BASE, EUSCI_B_I2C_TRANSMIT_INTERRUPT0);
			I2C_setMode(EUSCI_B1_BASE, EUSCI_B_I2C_RECEIVE_MODE);
			xferIndex = 0;
			I2C_masterReceiveStart(EUSCI_B1_BASE);
			I2C_enableInterrupt(EUSCI_B1_BASE, EUSCI_B_I2C_RECEIVE_INTERRUPT0);

		}

		/* Receives bytes into the receive buffer. If we have received all bytes,
		 * send a STOP condition */
		if (status & EUSCI_B_I2C_RECEIVE_INTERRUPT0)
		{
			if(xferIndex == NUM_OF_REG_BYTES+0x10 - 2)
			{
				I2C_masterReceiveMultiByteStop(EUSCI_B1_BASE);
				i2cRXData[xferIndex++] = I2C_masterReceiveMultiByteNext(EUSCI_B1_BASE);
			}
			else if(xferIndex == NUM_OF_REG_BYTES+0x10 - 1)
			{
				i2cRXData[xferIndex] = I2C_masterReceiveMultiByteNext(EUSCI_B1_BASE);
				I2C_disableInterrupt(EUSCI_B1_BASE, EUSCI_B_I2C_RECEIVE_INTERRUPT0);
				I2C_setMode(EUSCI_B1_BASE, EUSCI_B_I2C_TRANSMIT_MODE);
				xferIndex = 0;
				I2C_enableInterrupt(EUSCI_B1_BASE, EUSCI_B_I2C_TRANSMIT_INTERRUPT0); //For the next one.
				MAP_Interrupt_disableSleepOnIsrExit();
			}
			else
			{
				i2cRXData[xferIndex++] = I2C_masterReceiveMultiByteNext(EUSCI_B1_BASE);
			}
		}
	}
}

int main(void)
{
	volatile int i, j, temp, commandData, vnaMode, fMin, fMax, numPts, commandLine =0;
	volatile uint16_t test[NUM_ADC14_CHANNELS];
    /* Halting WDT  */
    MAP_WDT_A_holdTimer();

    MAP_FPU_enableModule();
    MAP_FPU_enableLazyStacking();
/*
    FPU_disableModule();
    FPU_disableStacking();
*/

    //MAP_Interrupt_enableSleepOnIsrExit();


    while(!initializeBackChannelUART())
    {
		for(i=0;i<100;i++);  /*Wait to try again. */
	}

    while(!initializeADC())
    {
		for(i=0;i<100;i++); // Wait to try again.
	}

	Interrupt_enableMaster();

     /* Enabling the FPU for floating point operation */
    while(!initializeDDS())
    {
    	for(i=0;i<100;i++);  //Wait to try again.
    }

    while(!initializeVersaclock())
    {
    	for(i=0;i<100;i++);  //Wait to try again.
    }

    while(!initializeI2C())
    {
    	for(i=0;i<100;i++);  //Wait to try again.
    }

    setDDSFrequency(1000000); // Test the DDS out.
    initVersaClock1MHz();

    dumpI2C();
    printf("Dumping Versaclock RAM after setting to 1MHz.\n");
    printf("Address   Received    Written");
    for (i=0x10;i<NUM_OF_REG_BYTES+0x10;i++)
    {
    	printf("%x    %x       %x\n",i,i2cRXData[i],
    			versaClockRegisters.init1MHzRegisterValues[i-0x10]);
    	if(i2cRXData[i]!=versaClockRegisters.init1MHzRegisterValues[i-0x10])
    		printf("They don't match!\n");
    }

    setDDSFrequency(10000000);
    if(!updateVersaclockRegs(10000000))
    	printf("updateVersaClockRegs failed!\n");
    dumpI2C();

    printf("Address,  Read,    Tried to Write\n");
    for (i=0;i<NUM_OF_CHANGED_REG_BYTES; i++)
    {
    		printf("%x       %x        %x\n",versaClockRegisters.changedAddresses[i],
    				i2cRXData[versaClockRegisters.changedAddresses[i]],
					versaClockRegisters.registerValues[12][i]);
    		if(i2cRXData[versaClockRegisters.changedAddresses[i]]!=
    				versaClockRegisters.registerValues[12][i])
    			printf("VersaClock Registers did NOT match!\n");
    }
    /*		Pulse the start of a conversion.	*/

    /*    while(!MAP_ADC14_toggleConversionTrigger()){
    	for(i=0;i<100;i++);  // Wait for conversion to finish.
    }

 		for(i=0;i<1000;i++){
    			temp = i*temp;
    		}*/
    /*		printf("\r\n Results are:\r\n");*/
    /*r(i=0; i<NUM_ADC14_CHANNELS; i++){
    				printf("ADC # %d  ",i);
    			printf("Result: %d\n",resultsBuffer[i]);
    }*/
    //MAP_PCM_gotoLPM0();
    /* Main while loop */
	while(1)
	{
		if(uartEndOfLineFlag)  /* Parse this command line. */
		{
			commandData = atoi(uartRXData);
			switch(commandLine)
			{
			case 0:
				if((commandData == 0)||(commandData == 1))
				{
					vnaMode = commandData;
					commandLine++;
				}
				else
				{
					/* Error occurred, something sent unexpected. */
				}
				break;
			case 1:
				fMin = commandData/DDS_RATIO;
				commandLine++;
				break;
			case 2:
				numPts = commandData;
				commandLine++;
			case 3:
				fMax = commandData/DDS_RATIO;
				commandLine =0;
				if(vnaMode==REFLECTION_MODE)
					reflectionMeasure(fMin,fMax,numPts);
				else
					transmissionMeasure(fMin,fMax,numPts);
			default:
				/* Don't expect to be here.  */
				break;
			}
		}
	}
}

void initializeClocks(void)
{
    /* Initialize main clock to 48MHz.  To make it 3 MHz change the 48 to 3
     * and the 16's to 1.*/
    CS_setDCOCenteredFrequency(CS_DCO_FREQUENCY_48); // Full speed
    CS_initClockSignal(CS_MCLK, CS_DCOCLK_SELECT, CS_CLOCK_DIVIDER_16 );
    MAP_CS_initClockSignal(CS_HSMCLK, CS_DCOCLK_SELECT, CS_CLOCK_DIVIDER_16 );
    MAP_CS_initClockSignal(CS_SMCLK, CS_DCOCLK_SELECT, CS_CLOCK_DIVIDER_16 );
}

int initializeBackChannelUART(void){

	initializeClocks();
    /* Selecting P1.2 and P1.3 in UART mode. */
    MAP_GPIO_setAsPeripheralModuleFunctionInputPin(GPIO_PORT_P1,
        GPIO_PIN2 | GPIO_PIN3, GPIO_PRIMARY_MODULE_FUNCTION);

    /* Configuring UART Module */
    if(MAP_UART_initModule(EUSCI_A0_BASE, &uartConfig)==STATUS_FAIL)
    	return (STATUS_FAIL);

    /* Enable UART module */
    MAP_UART_enableModule(EUSCI_A0_BASE);

    /* Enable UART interrupts for backchannel UART
     * We may or may not need to do this.  The simple
     * printf() routine doesn't seem to use it.  */
    UART_enableInterrupt(EUSCI_A0_BASE, EUSCI_A_UART_RECEIVE_INTERRUPT);
    		/*EUSCI_A_SPI_TRANSMIT_INTERRUPT);*/
    Interrupt_enableInterrupt(INT_EUSCIA0);
    return 1;
}

int initializeADC(void){
    /* Initializing ADC (MCLK/1/1) */
    ADC14_enableModule();
    ADC14_initModule(ADC_CLOCKSOURCE_MCLK, ADC_PREDIVIDER_1, ADC_DIVIDER_1,
            ADC_NOROUTE);

    /* Configuring GPIOs for Analog In

     * Pin 5.0 is S11_I, A5  resultsBuffer[0]
     * Pin 5.1 is S11_Q, A3  resultsBuffer[1]
     * Pin 4.3 is S21_I, A10 resultsBuffer[2]
     * Pin 4.1 is S21_Q, A12 resultsBuffer[3] */

    GPIO_setAsPeripheralModuleFunctionInputPin(GPIO_PORT_P5,
             GPIO_PIN1| GPIO_PIN0, GPIO_TERTIARY_MODULE_FUNCTION);
    GPIO_setAsPeripheralModuleFunctionInputPin(GPIO_PORT_P4,
            GPIO_PIN1 | GPIO_PIN3, GPIO_TERTIARY_MODULE_FUNCTION);

    /* Configuring ADC Memory (ADC_MEM0 - ADC_MEM3, with A12, A10, A5, A3
     * with no repeat) with VCC and VSS reference */
    if(!ADC14_configureMultiSequenceMode(ADC_MEM0, ADC_MEM3, false))
    	return(0);

    if(!ADC14_configureConversionMemory(ADC_MEM0,
            	VREF,
				ADC_INPUT_A5, ADC_NONDIFFERENTIAL_INPUTS))
    	return(0);
    if(!ADC14_configureConversionMemory(ADC_MEM1,
                VREF,
                ADC_INPUT_A3, ADC_NONDIFFERENTIAL_INPUTS))
        return(0);
    if(!ADC14_configureConversionMemory(ADC_MEM2,
                VREF,
                ADC_INPUT_A10, ADC_NONDIFFERENTIAL_INPUTS))
        		return(0);
    if(!ADC14_configureConversionMemory(ADC_MEM3,
                VREF,
                ADC_INPUT_A12, ADC_NONDIFFERENTIAL_INPUTS))
        return(0);

    /* Enabling the interrupt when a conversion on channel 3 (end of sequence)
     *  is complete and enabling conversions */
    ADC14_enableInterrupt(ADC_INT3);

    /* Enabling Interrupts */
    Interrupt_enableInterrupt(INT_ADC14);

    /* Setting up the sample timer to automatically step through the sequence
     * convert.
     */
    if(!MAP_ADC14_enableSampleTimer(ADC_AUTOMATIC_ITERATION))
    		return 0;

    /* Enable conversion */
    if(!MAP_ADC14_enableConversion())
    	return 0;

    return 1;
}

void pulseFQ_UD(void)
{
	MAP_GPIO_setOutputHighOnPin(GPIO_PORT_P4, GPIO_PIN6);
	MAP_GPIO_setOutputLowOnPin(GPIO_PORT_P4, GPIO_PIN6);
}

void pulse_W_CLK(void)
{
	MAP_GPIO_setOutputHighOnPin(GPIO_PORT_P1, GPIO_PIN5);
	MAP_GPIO_setOutputLowOnPin(GPIO_PORT_P1, GPIO_PIN5);
}

void pulse_DDS_RST(void)
{
	GPIO_setOutputHighOnPin(GPIO_PORT_P4, GPIO_PIN7);
	MAP_GPIO_setOutputLowOnPin(GPIO_PORT_P4, GPIO_PIN7);

}
#ifndef USE_SPI
void transmit_DDS_Byte(uint8_t data)
{ // Bit banging method of sending data to DDS.
	int i;
	for (i=0; i<8; i++, data>>=1) {
		if(data & 0x01)
		{
			MAP_GPIO_setOutputHighOnPin(GPIO_PORT_P1, GPIO_PIN6);
		}
		else
		{
			MAP_GPIO_setOutputLowOnPin(GPIO_PORT_P1, GPIO_PIN6);
		}
		pulse_W_CLK();
	}
}
#endif
int initializeDDS(void)
{
	/* This function initializes the DDS.  The first thing needed is to
	 * set the DDS into serial mode, which is done by pulsing W_CLK, and
	 * then FQ_UD.  Next the SPI is initialized.
	 */
	MAP_GPIO_setAsOutputPin(GPIO_PORT_P4, GPIO_PIN6|GPIO_PIN7); // Set FQ_UD, DDS_RST as output.
	MAP_GPIO_setAsOutputPin(GPIO_PORT_P1, GPIO_PIN5|GPIO_PIN6); // Set W_CLK initially as output.
	pulse_DDS_RST();
	// Set DDS to serial mode.
	pulse_W_CLK();
	pulseFQ_UD();
	// This concludes setting DDS to serial.
#ifdef USE_SPI
	/* Selecting P1.5 P1.6 and P1.7 in SPI mode */
	MAP_GPIO_setAsPeripheralModuleFunctionInputPin(GPIO_PORT_P1,
			GPIO_PIN5 | GPIO_PIN6 | GPIO_PIN7, GPIO_PRIMARY_MODULE_FUNCTION); // Not really using P1.7.
	/* Configuring SPI in 3wire master mode */
	MAP_SPI_initMaster(EUSCI_B0_BASE, &spiMasterConfig);
	/* Enable SPI module */
	MAP_SPI_enableModule(EUSCI_B0_BASE);
	/* Enabling interrupts */
	MAP_Interrupt_enableInterrupt(INT_EUSCIB0);
	MAP_Interrupt_enableSleepOnIsrExit();
#endif
	setDDSFrequency(0); // Safety for serial mode.
	return 1; // Need to come back here and make these all if loops if the function supports it.
}

int setDDSFrequency(long long frequency)
{
	/* This function sets the AD9851 frequency using SPI for the data and clock
	 * and P4.6 as FQ_UD. It requires the DDS already be in serial mode, which
	 * is set in the intitialization, which also sets the P6.4 and P6.4 up to do
	 * SPI.  40 bits are sent (5 bytes via SPI) before FQ_UD is pulsed.  The
	 * AD9851 can handle data faster than we can send it via SPI.
	 */
	int i;
	unsigned long long tuning_word = roundl((frequency << 32) / 180000000);
	if((frequency<1000000)||(frequency>70000000)) return 1; // Frequency out of range.
#ifdef USE_SPI
	for (i=0;i<4;i++,tuning_word >>=8) // Send the frequency words
	{
		while (!(MAP_SPI_getInterruptStatus(EUSCI_B0_BASE,EUSCI_B_SPI_TRANSMIT_INTERRUPT)));
		MAP_SPI_transmitData ( EUSCI_B0_BASE, (uint8_t)((tuning_word)&(long long)0xff) );
	}
	MAP_SPI_transmitData ( EUSCI_B0_BASE, (uint8_t)(1) ); //O phase, 6X multiply
#else // Bitbanging below:
		for (i=0;i<4;i++,tuning_word >>=8) // Send the frequency words
		{
			transmit_DDS_Byte( (uint8_t)((tuning_word)&(long long)0xff) );
		}
		transmit_DDS_Byte( (uint8_t)(1) ); //O phase, 6X multiply
#endif
	pulseFQ_UD();
	return 1;
}

/*
 * Initialize Versaclock.
 */
int initializeVersaclock(void)
{

	MAP_GPIO_setAsOutputPin(GPIO_PORT_P5, GPIO_PIN5|GPIO_PIN4); // Outputs for CKSEL and SD.

	MAP_GPIO_setOutputHighOnPin(GPIO_PORT_P5, GPIO_PIN4|GPIO_PIN5);
	MAP_GPIO_setOutputLowOnPin(GPIO_PORT_P5, GPIO_PIN5);

	 /* Wait for 10 ms for Versaclock to power up. */
	volatile long int i,j;
	for(i=0;i<6400; i++)  //Need to delay at least 10 ms.  This is just a guess at that.
	{
		j=j+100*j/(i+1)+i;
	}
	return 1;
}
/*
 * Initialize I2C for communications with VersaClock.
 */
int initializeI2C(void)
{
    /* Select Port 6 for I2C - Set Pin 4, 5 to input Primary Module Function,
     *   (UCB1SIMO/UCB1SDA, UCB1SOMI/UCB1SCL).
     */
    MAP_GPIO_setAsPeripheralModuleFunctionInputPin(GPIO_PORT_P6,
            GPIO_PIN5 + GPIO_PIN4, GPIO_PRIMARY_MODULE_FUNCTION);

    memset(i2cRXData, 0x00, NUM_OF_REG_BYTES+0x10); // Start with 0 so we can see the changes.

    /* Initializing I2C Master to parameters in i2cConfig */
    I2C_initMaster(EUSCI_B1_BASE, &i2cConfig);

    /* Specify slave address */
    I2C_setSlaveAddress(EUSCI_B1_BASE, SLAVE_ADDRESS);

    /* Set Master in transmit mode */
    I2C_setMode(EUSCI_B1_BASE, EUSCI_B_I2C_TRANSMIT_MODE);

    /* Enable I2C Module to start operations */
    I2C_enableModule(EUSCI_B1_BASE);
    /* Enable and clear the interrupt flag */
    I2C_clearInterruptFlag(EUSCI_B1_BASE,
            EUSCI_B_I2C_TRANSMIT_INTERRUPT0 + EUSCI_B_I2C_RECEIVE_INTERRUPT0
			+ EUSCI_B_I2C_NAK_INTERRUPT);
    //Enable master Transmit interrupt
    I2C_enableInterrupt(EUSCI_B1_BASE, EUSCI_B_I2C_TRANSMIT_INTERRUPT0
    		+ EUSCI_B_I2C_NAK_INTERRUPT);
    //MAP_Interrupt_enableSleepOnIsrExit();
    Interrupt_enableInterrupt(INT_EUSCIB1);
    return 1;
}

/*
 *This routine dumps all the registers of the VersaCLock.
 */
void dumpI2C(void)
{
    /* Making sure the last transaction has been completely sent out */
    while ((I2C_masterIsStopSent(EUSCI_B1_BASE) == EUSCI_B_I2C_SENDING_STOP)||
    		(TXByteCtr!=0));

	justSending=false;  // We want to receive data back.

	/* See the following address for info as to why this is different that the example.
     * https://e2e.ti.com/support/microcontrollers/msp430/f/166/p/462976/1666648
     */
    I2C_masterSendMultiByteStart(EUSCI_B1_BASE, 0x00);

    /* Enabling transfer interrupt after stop has been sent */
    I2C_enableInterrupt(EUSCI_B1_BASE, EUSCI_B_I2C_TRANSMIT_INTERRUPT0);

    /* While the stop condition hasn't been sent out... */
/*

    MAP_PCM_gotoLPM0InterruptSafe();
*/
}

/*
 * This routine sends all the registers to initialize the VersaClock to 1MHz in and 1MHz out
 * with 0 and 90 degrees difference on the output phases.
 */
void initVersaClock1MHz(void)
{
	writeVersaClockBlock(versaClockRegisters.init1MHzRegisterValues, firstReg, NUM_OF_REG_BYTES);
}

/* Send a block of data, bumBytes long and store it in the I2C address at blockStart.
 * The firstDataPtr is a pointer to the memory address where the first data byte is.
 * The blockStart variable is the address in the versaclock where the data starts.
 * The numBytes is the numberof bytes to send.
 */
void writeVersaClockBlock(const uint8_t *firstDataPtr, uint8_t blockStart, uint8_t numBytes)
{
	volatile int i;

	/* Making sure the last transaction has been completely sent out */
    while (I2C_masterIsStopSent(EUSCI_B1_BASE) == EUSCI_B_I2C_SENDING_STOP);

	justSending=true;
	TXData = firstDataPtr;
    TXByteCtr = numBytes;
    xferIndex = 0;

    //Enable master Transmit interrupt
    I2C_enableInterrupt(EUSCI_B1_BASE, EUSCI_B_I2C_TRANSMIT_INTERRUPT0
    		+ EUSCI_B_I2C_NAK_INTERRUPT);

    I2C_masterSendMultiByteStart(EUSCI_B1_BASE, blockStart); // Send the address.
}

int updateVersaclockRegs(long int frequency)
{
	int i,j, offset = 0;
	volatile int m;
	static int presentBandIndex=0;
	frequency = frequency/1000;

	if((versaClockRegisters.frequencyBandLimit[presentBandIndex] <= frequency)&
			(frequency<versaClockRegisters.frequencyBandLimit[presentBandIndex+1])) return 1;
	for(i=0;i<NUM_BANDS;i++)
	{
		if((versaClockRegisters.frequencyBandLimit[i] <= frequency)&
				(frequency<versaClockRegisters.frequencyBandLimit[i+1]))
		{
			presentBandIndex = i;  // We found the band.
			for(j=0;j<NUM_BAND_BLOCKS;j++)
			{
				writeVersaClockBlock(&(versaClockRegisters.registerValues[i][offset]),
						versaClockRegisters.blockFirstAddress[j],
						versaClockRegisters.blockNumBytes[j]);
				for(m=0;m<100;m++);
				offset += versaClockRegisters.blockNumBytes[j];
			}
		}
	}
	return 1;
}

/* Measure the reflection coefficient at numPts between fMin and fMax. */
void reflectionMeasure(int fMin,int fMax,int numPts)
{
	int i;
	int f = fMin;
	int deltaF = (fMax-fMin)/numPts;
	int16_t s11R, s11I;
	uint8_t s11RH,s11RL,s11IH,s11IL;
	for(i=0;i<numPts;i++)
	{
		/* Set oscillators */
		setDDSFrequency((long long)f);
		updateVersaclockRegs(f);
		f+=deltaF;
		/* measure ADC14 */
		while(!MAP_ADC14_toggleConversionTrigger())
		{
		    	for(i=0;i<100;i++);  // Wait for conversion to finish.
		}
		s11R = (resultsBuffer[0]-8192)*4;
		s11I = (resultsBuffer[1]-8192)*4;
		s11RH = (uint8_t)((s11R & 0xff00)>>8);
		s11RL = (uint8_t)(s11R & 0x00ff);
		printf("%c,%c",s11RL,s11RH);
		s11RH = (uint8_t)((s11I & 0xff00)>>8);
		s11RL = (uint8_t)(s11I & 0x00ff);
		printf("%c,%c",s11IL,s11IH);
	}

}

/* Measure the transmission coefficient at numPts between fMin and fMax. */
void transmissionMeasure(int fMin,int fMax,int numPts)
{
	int i;
	int f = fMin;
	int deltaF = (fMax-fMin)/numPts;
	int16_t s21R, s21I;
	uint8_t s21RH,s21RL,s21IH,s21IL;
	for(i=0;i<numPts;i++)
	{
		/* Set oscillators */
		setDDSFrequency((long long)f);
		updateVersaclockRegs(f);
		f+=deltaF;
		/* measure ADC14 */
		while(!MAP_ADC14_toggleConversionTrigger())
		{
		    	for(i=0;i<100;i++);  // Wait for conversion to finish.
		}
		s21R = (resultsBuffer[2]-8192)*4;
		s21I = (resultsBuffer[3]-8192)*4;
		s21RH = (uint8_t)((s21R & 0xff00)>>8);
		s21RL = (uint8_t)(s21R & 0x00ff);
		printf("%c,%c",s21RL,s21RH);
		s21RH = (uint8_t)((s21I & 0xff00)>>8);
		s21RL = (uint8_t)(s21I & 0x00ff);
		printf("%c,%c",s21IL,s21IH);
	}

}
