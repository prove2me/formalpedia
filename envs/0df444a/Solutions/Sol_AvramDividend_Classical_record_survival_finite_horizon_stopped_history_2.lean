-- Prove2me | solution 2 for AvramDividend.Classical.record_survival_finite_horizon_stopped_history
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:07:57.342231+00:00
-- url     : https://prove2.me/submissions/f97e313b-5ead-4f89-9f32-e6fcad59ae25

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (M : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const M).measurableSpace]
      {ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (M : ℝ≥0∞)} := by 
  have h1 := upperPassage_stopping_rightCont_filtration X b
  have := (IsStoppingTime.measurableSet_inter_le_const_iff h1 _ M).1
    ((record_survival_stopped_history_measurable X a b).inter (h1.measurableSet_le' M))
  exact this
