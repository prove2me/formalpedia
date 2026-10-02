-- Prove2me | solution 4 for ErlerGross.B3_digamma_values
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:55:13.001018+00:00
-- url     : https://prove2.me/submissions/39d98194-2e76-47d7-95b6-9a381ecd7513

import Mathlib
import Theorems.Thm_ErlerGross_digamma_sum_thirds
open Real

theorem solution :
    Complex.digamma ((2 : Complex) / 3) / 2 + Complex.digamma ((1 : Complex) / 3) / 2 -
      Complex.digamma ((1 : Complex) / 2) = ((-Real.log (27 / 16) / 2 : Real) : Complex) := by
  have hGauss := ErlerGross.digamma_sum_thirds
  rw [Complex.digamma_one_half]
  rw [show Complex.digamma ((2 : Complex) / 3) / 2 + Complex.digamma ((1 : Complex) / 3) / 2 = (Complex.digamma ((1 : Complex) / 3) + Complex.digamma ((2 : Complex) / 3)) / 2 by ring]
  rw [hGauss, Complex.digamma_one]
  rw [show Complex.log (2 : Complex) = (Real.log 2 : Complex) by exact (Complex.ofNat_log (n := 2)).symm]
  push_cast
  rw [Real.log_div (by norm_num) (by norm_num)]
  have h27 : Real.log (27 : Real) = 3 * Real.log 3 := by
    rw [show (27 : Real) = 3 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have h16 : Real.log (16 : Real) = 4 * Real.log 2 := by
    rw [show (16 : Real) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h27, h16]
  push_cast
  ring
