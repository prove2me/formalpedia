-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_real_nnreal_mesh_quotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:49:41.207593+00:00
-- url     : https://prove2.me/submissions/e2cb5bbc-e64c-4dd1-a06b-10e245fa60f6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The original real positive uniform width commutes with the NNReal
embedding of its nonnegative numerator. -/
theorem solution
    (T : ℝ≥0) (n : ℕ) :
    Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / Real.toNNReal ((n : ℝ) + 1) := by
  simpa using
    (Real.toNNReal_div (x := (T : ℝ)) (y := (n : ℝ) + 1) (by positivity))
