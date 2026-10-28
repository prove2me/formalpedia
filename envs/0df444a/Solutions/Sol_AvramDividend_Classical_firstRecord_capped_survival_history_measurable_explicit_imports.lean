-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_survival_history_measurable_explicit_imports
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:41:39.498028+00:00
-- url     : https://prove2.me/submissions/ccddc337-6864-4c8a-8113-6af53f1d41ec

import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable
import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Localise strict-record survival in the finite stopping-time history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const N).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by
  exact stoppingTime_capped_history_event_measurable
    (upperPassage_stopping_rightCont_filtration X b)
    {ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω}
    (record_survival_stopped_history_measurable X a b) N