-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_source_capped_lower_killed_history_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:14:42.644673+00:00
-- url     : https://prove2.me/submissions/47418aea-27a4-497a-be4a-bddd9bec22f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual capped record clock and lower-killed source prefix are measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (N : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) ∧
    MeasurableSet
      ({ω : Ω | twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by
  constructor
  · exact firstRecord_truncation_clock_measurable X b N
  · have hUpper : Measurable (twoSidedExitUpTime X b) := by
      have hs := (upperPassage_stopping_rightCont_filtration X b).measurable_iSup
      exact hs.mono (iSup_le fun i => 𝓕.rightCont.le i) le_rfl
    have hLower : Measurable (twoSidedExitDownTime X lower) := by
      have hs := (avram_ws01h_lowerPassage_stopping_rightCont_filtration
        X lower).measurable_iSup
      exact hs.mono (iSup_le fun i => 𝓕.rightCont.le i) le_rfl
    exact (measurableSet_lt hUpper hLower).inter
      (measurableSet_le hUpper measurable_const)
