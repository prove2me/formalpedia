-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_scaled_cutoff_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:41:13.869012+00:00
-- url     : https://prove2.me/submissions/b60202e7-cb20-4b42-a303-9073b45bd227

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite time scaling preserves finite measure mass below any separated cutoff. -/
theorem solution
    (ν : Measure ℝ) (c : ℝ) (hνfin : ν (Iic c) ≠ ⊤)
    (T : ℝ≥0) :
    (((T : ℝ≥0∞) • ν) (Iic c)) ≠ ⊤ := by
  have hT : (T : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  simpa only [Measure.smul_apply, smul_eq_mul] using
    (ENNReal.mul_ne_top hT hνfin)
