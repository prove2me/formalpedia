-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_clock_length_ofReal_eq_NNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:19:36.806104+00:00
-- url     : https://prove2.me/submissions/24301074-8f7c-4079-a377-c864755e9940

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t : ℝ≥0) (hst : s ≤ t) :
    ENNReal.ofReal ((t : ℝ) - (s : ℝ)) =
      ((t - s : ℝ≥0) : ℝ≥0∞) := by
  rw [← NNReal.coe_sub hst]
  exact ENNReal.ofReal_coe_nnreal
