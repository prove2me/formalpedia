-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_quadratic_tail_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:25:33.521854+00:00
-- url     : https://prove2.me/submissions/1aea5195-4385-4547-8cd1-5d229e07b5ea

import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The large-value tail of a nonnegative random variable is pointwise
dominated by its square divided by the positive threshold.
-/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (R y : ℝ) (hR : 0 < R) (hy : 0 ≤ y) :
    (if R ≤ y then y else 0) ≤ y ^ 2 / R := by
  by_cases h : R ≤ y
  · rw [if_pos h]
    apply (le_div_iff₀ hR).2
    nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
  · rw [if_neg h]
    exact div_nonneg (sq_nonneg y) (le_of_lt hR)
