-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exponential_remainder_divided_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:42:20.521408+00:00
-- url     : https://prove2.me/submissions/d8e546d8-00f4-4ab6-854a-ce6ad9e5c7d0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_exponential_remainder_integral_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory intervalIntegral Set

theorem solution (s z : ℝ) (hs : 0 < s) :
    (Real.exp (-(s * z)) - 1 + s * z) / s =
      ∫ t in (0 : ℝ)..z, (1 - Real.exp (-(s * t))) := by
  apply (div_eq_iff (ne_of_gt hs)).2
  simpa only [mul_comm] using
    (esscher_exponential_remainder_integral_kernel s z).symm
