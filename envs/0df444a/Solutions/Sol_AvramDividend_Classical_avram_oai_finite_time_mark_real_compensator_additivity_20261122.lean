-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_finite_time_mark_real_compensator_additivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:56:40.552172+00:00
-- url     : https://prove2.me/submissions/d3cfd163-cd15-4366-b5f2-8d22816fe088

import Mathlib
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (s t : ℝ≥0) (hst : s ≤ t) (m : ℝ≥0∞) :
    ((t : ℝ≥0∞) * m).toReal =
      ((s : ℝ≥0∞) * m).toReal +
        (((t - s : ℝ≥0) : ℝ≥0∞) * m).toReal  := by
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [NNReal.coe_sub hst]
  ring
