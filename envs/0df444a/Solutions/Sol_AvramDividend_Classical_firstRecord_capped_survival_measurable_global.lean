-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_survival_measurable_global
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:23:02.070602+00:00
-- url     : https://prove2.me/submissions/d631a8a9-6c62-4b3f-a9e6-21b8f7a1a74e

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by 
  exact (isStoppingTime_withTop_of_le_events _ (firstRecord_truncation_stopping_rightCont X b N)).measurableSpace_le _
    (firstRecord_capped_survival_in_finiteStoppedHistory X a b N)
