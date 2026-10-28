-- Prove2me | solution 1 for AvramDividend.Classical.upperPassage_capped_stopping_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:17:01.395422+00:00
-- url     : https://prove2.me/submissions/ac6f6185-c264-4b57-af3f-ed2277e3513a

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)) := by 
  exact (upperPassage_stopping_rightCont_filtration X b).min_const N
