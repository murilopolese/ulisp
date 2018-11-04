# uLisp

A version of the Lisp programming language for ATmega-based Arduino boards.
For more information see:
http://www.ulisp.com/

## Quirkbot

This version of uLisp is optimized to run on Quirkbots (atmega32u4).

The original uLisp implementation made reference to hardware and features that are not present on Quirkbot and were removed.

Even after removing those references, uLisp was still too big to be flashed and the functions related to string manipulation, editor and "notes" were removed.

The main changes are:
- Remove SPI, I2C and SDCARD
- Remove string manipulation
- Remove notes (this might come back eventually)
- Remove tree editor
