-- Prove2me | solution 1 for ErlerGross.B3_digamma_triplication_formula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T16:30:21.71787+00:00
-- url     : https://prove2.me/submissions/0d8a84b8-1391-4aa9-a50f-b3cb666ebd66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ErlerGross_digamma_multiplication_formula

theorem solution (z : Complex) (hz : 0 < z.re) :
    Complex.digamma z + Complex.digamma (z + (1 : Complex) / 3) +
      Complex.digamma (z + (2 : Complex) / 3) =
        3 * Complex.digamma (3 * z) - 3 * (Real.log 3 : Complex) := by
  have h := ErlerGross.digamma_multiplication_formula 3 (by norm_num) z hz
  simpa [Finset.sum_range_succ] using h
