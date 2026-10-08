-- Prove2me | solution 1 for AvramDividend.Classical.negative_exponential_increment_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:24:14.06032+00:00
-- url     : https://prove2.me/submissions/7422b3fd-25ae-4262-af18-539e44d841b3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y ≤ 0) :
    ‖Real.exp (θ * y) - 1‖ ≤ (1 : ℝ) := by
  have hθy : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy
  have he : 0 ≤ Real.exp (θ * y) := Real.exp_nonneg _
  have he1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hθy
  rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr he1)]
  linarith
