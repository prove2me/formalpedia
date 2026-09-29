-- Prove2me | solution 3 for ErlerGross.B3_digamma_values
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:54:22.781466+00:00
-- url     : https://prove2.me/submissions/b35e85ab-25c4-47d3-8407-84ca14852a00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
