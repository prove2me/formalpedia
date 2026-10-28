-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_survival_history_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:48:41.637989+00:00
-- url     : https://prove2.me/submissions/cc656938-9a7a-43e5-bff6-f75e6254368e

import Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable
import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const N).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by 
  exact stoppingTime_capped_history_event_measurable _ _ (record_survival_stopped_history_measurable X a b) N
