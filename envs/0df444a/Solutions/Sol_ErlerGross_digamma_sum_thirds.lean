-- Prove2me | solution 1 for ErlerGross.digamma_sum_thirds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:06:12.535848+00:00
-- url     : https://prove2.me/submissions/5ef1c70a-0c4b-4e8a-b536-c0e1cbbee3b7

import Mathlib
import Theorems.Thm_ErlerGross_B3_digamma_triplication_formula

theorem solution :
    Complex.digamma ((1 : Complex) / 3) + Complex.digamma ((2 : Complex) / 3) =
      2 * Complex.digamma 1 - (3 : Complex) * (Real.log 3 : Complex) := by
  have htrip := ErlerGross.B3_digamma_triplication_formula ((1 : Complex) / 3) (by norm_num)
  rw [Complex.ofReal_log (by positivity : (0 : Real) <= 3)]
  have h := htrip
  norm_num at h
  linear_combination h