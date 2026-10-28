-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:46:59.460242+00:00
-- url     : https://prove2.me/submissions/be4de6e3-4874-43b7-b511-586f267ad6ce

import Theorems.Thm_AvramDividend_Classical_downExitTime_zero_implies_near_threshold_crossings
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_near_threshold_crossings
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact arbitrary-threshold criterion for an instantaneous strict first passage. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) :
    twoSidedExitDownTime X b ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b := by
  constructor
  · exact downExitTime_zero_implies_near_threshold_crossings X b ω
  · exact twoSidedExitDownTime_eq_zero_of_near_threshold_crossings X b ω
