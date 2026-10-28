-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_truncation_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:37:45.91599+00:00
-- url     : https://prove2.me/submissions/ac3bffa1-81b7-4393-b5d6-70a029096ee5

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (M : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (min (twoSidedExitUpTime X b ω) (M : ℝ≥0∞)).toNNReal) := by 
  have h := (upperPassage_stopping_rightCont_filtration X b).measurable_iSup
  have h' : Measurable (twoSidedExitUpTime X b) :=
    h.mono (iSup_le fun i => 𝓕.rightCont.le i) le_rfl
  exact (h'.min measurable_const).ennreal_toNNReal
