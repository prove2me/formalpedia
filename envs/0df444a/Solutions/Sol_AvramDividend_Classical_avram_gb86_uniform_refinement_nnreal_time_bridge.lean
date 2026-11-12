-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb86_uniform_refinement_nnreal_time_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:31:35.231119+00:00
-- url     : https://prove2.me/submissions/43425ac6-684d-4acd-9a02-128b4fee292f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open scoped NNReal

/-- A coarse uniform time point is also a point on its product refinement. -/
theorem solution (n m b i : ℕ) (hb : 0 < b) :
    (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) =
    ((i * b : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hm0 : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
  push_cast
  field_simp
