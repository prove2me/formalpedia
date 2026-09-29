-- Prove2me | solution 1 for ErlerGross.B3_digamma_values
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:52:40.410383+00:00
-- url     : https://prove2.me/submissions/44438f21-0b2a-485e-b921-e3705770d768
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ErlerGross_B3_digamma_triplication_formula

theorem solution :
    Complex.digamma ((2 : Complex) / 3) / 2 + Complex.digamma ((1 : Complex) / 3) / 2 -
      Complex.digamma ((1 : Complex) / 2) = ((-Real.log (27 / 16) / 2 : Real) : Complex) := by
  have htrip := ErlerGross.B3_digamma_triplication_formula ((1 : Complex) / 3) (by norm_num)
  have hvals : Complex.digamma ((1 : Complex) / 3) +
      Complex.digamma ((2 : Complex) / 3) =
      2 * Complex.digamma 1 - 3 * (Real.log 3 : Complex) := by
    have h := htrip
    norm_num at h
    have hlog3 : Complex.log (3 : Complex) = (Real.log 3 : Complex) :=
      (Complex.ofReal_log (by positivity)).symm
    rw [hlog3] at h
    linear_combination h
  have hpair : Complex.digamma ((2 : Complex) / 3) / 2 +
      Complex.digamma ((1 : Complex) / 3) / 2 =
      Complex.digamma 1 - (3 / 2 : Complex) * (Real.log 3 : Complex) := by
    calc
      _ = (Complex.digamma ((1 : Complex) / 3) +
          Complex.digamma ((2 : Complex) / 3)) / 2 := by ring
      _ = (2 * Complex.digamma 1 - 3 * (Real.log 3 : Complex)) / 2 := by rw [hvals]
      _ = _ := by ring
  rw [hpair, Complex.digamma_one, Complex.digamma_one_half]
  have hlog2 : Complex.log (2 : Complex) = (Real.log 2 : Complex) :=
    (Complex.ofReal_log (by positivity)).symm
  rw [hlog2]
  rw [show (27 : Real) / 16 = (3 : Real) ^ 3 / 2 ^ 4 by norm_num,
    Real.log_div (by positivity) (by positivity)]
  rw [Real.log_pow, Real.log_pow]
  push_cast
  ring
