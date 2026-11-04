-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:23:50.179546+00:00
-- url     : https://prove2.me/submissions/489702a5-9990-4b2a-9f24-7b9cfa730cdd

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- The real-to-NNReal grid clock from the expectation theorem agrees
exactly with the canonical original NNReal uniform-grid clock. -/
theorem solution
    (T : ℝ≥0) (n : ℕ) :
    Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / ((n : ℝ≥0) + 1) := by
  have hnonneg : 0 ≤ (T : ℝ) / ((n : ℝ) + 1) :=
    div_nonneg T.property (by positivity)
  apply NNReal.eq
  rw [Real.coe_toNNReal _ hnonneg, NNReal.coe_div]
  norm_cast
