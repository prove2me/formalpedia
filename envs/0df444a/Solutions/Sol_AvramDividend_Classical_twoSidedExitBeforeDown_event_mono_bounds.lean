-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitBeforeDown_event_mono_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:27:05.045869+00:00
-- url     : https://prove2.me/submissions/87db05c5-e539-4316-86d5-84377831c066

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_antitone_threshold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Tightening both strict two-sided exit boundaries shrinks the favourable event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (alo ahi blo bhi : ℝ) (hu : alo ≤ ahi) (hd : blo ≤ bhi) :
    {ω : Ω | twoSidedExitUpTime X ahi ω < twoSidedExitDownTime X bhi ω} ⊆
      {ω : Ω | twoSidedExitUpTime X alo ω < twoSidedExitDownTime X blo ω} := by
  intro ω hω
  have hupper := twoSidedExitUpTime_mono_threshold X alo ahi hu ω
  have hlower := twoSidedExitDownTime_antitone_threshold X blo bhi hd ω
  exact lt_of_lt_of_le (lt_of_le_of_lt hupper hω) hlower
