-- Prove2me | solution 2 for AvramDividend.Classical.firstRecord_truncation_stopping_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:04:10.976989+00:00
-- url     : https://prove2.me/submissions/9ac8be85-90a5-47ed-ad2f-c855a0146e84

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_extendedStopping_truncate_finite_leEvents

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (M : ℝ≥0) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s]
        {ω : Ω | (min (twoSidedExitUpTime X b ω) (M : ℝ≥0∞)).toNNReal ≤ s} := by 
  exact extendedStopping_truncate_finite_leEvents _ (upperPassage_stopping_rightCont_filtration X b) M
