-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_survival_in_finiteStoppedHistory
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:06:39.692411+00:00
-- url     : https://prove2.me/submissions/128c0a7c-82e3-4bbe-a573-f6065f9e2cff

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_history_measurable_explicit_imports

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      (isStoppingTime_withTop_of_le_events
        (fun ω : Ω => (min (twoSidedExitUpTime X b ω)
          (N : ℝ≥0∞)).toNNReal)
        (firstRecord_truncation_stopping_rightCont X b N)).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by 
  exact stoppedHistory_measurable_of_equal_finite_clocks (𝓕 := 𝓕.rightCont) _
    (firstRecord_truncation_stopping_rightCont X b N) _
    ((upperPassage_stopping_rightCont_filtration X b).min_const N)
    (fun ω => firstRecord_capped_coe_toNNReal_with_measure_import X b N ω) _
    (firstRecord_capped_survival_history_measurable_explicit_imports X a b N)
