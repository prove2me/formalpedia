-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_original_record_survival_stopped_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:55:51.35087+00:00
-- url     : https://prove2.me/submissions/c8a70142-5500-4a97-aa5b-22005ab50b2c

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original lower-ruin/upper-record comparison is a measurable
    killed prefix at the capped first-upcrossing history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const N).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by
  let hUp := upperPassage_stopping_rightCont_filtration X b
  have hDown : IsStoppingTime 𝓕.rightCont (twoSidedExitDownTime X lower) := by
    apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    intro t
    have hEq :
        {ω : Ω | twoSidedExitDownTime X lower ω < (t : ℝ≥0∞)} =
        {ω : Ω | ∃ s : ℝ≥0, s < t ∧ X.X s ω < lower} := by
      ext ω
      change
        (⨅ (s : ℝ≥0) (_ : X.X s ω < lower), (s : ℝ≥0∞)) <
          (t : ℝ≥0∞) ↔
        ∃ s : ℝ≥0, s < t ∧ X.X s ω < lower
      exact lowerCrossingClock_lt_horizon_iff_exists_witness X lower ω t
    have hOriginal :
        MeasurableSet[𝓕 t]
          {ω : Ω | twoSidedExitDownTime X lower ω < (t : ℝ≥0∞)} := by
      rw [hEq]
      exact levy_lowerCrossing_before_filtration_measurable X lower t
    exact (𝓕.le_rightCont t) _ hOriginal
  have hBefore :
      MeasurableSet[hUp.measurableSpace]
        {ω : Ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} := by
    have hLe : MeasurableSet[hUp.measurableSpace]
        {ω : Ω | twoSidedExitDownTime X lower ω ≤ twoSidedExitUpTime X b ω} := by
      exact hDown.measurableSet_stopping_time_le hUp
    convert hLe.compl using 1
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  exact stoppingTime_capped_history_event_measurable hUp _ hBefore N
