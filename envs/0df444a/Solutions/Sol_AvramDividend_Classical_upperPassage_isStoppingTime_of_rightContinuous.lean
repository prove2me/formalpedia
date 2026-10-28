-- Prove2me | solution 1 for AvramDividend.Classical.upperPassage_isStoppingTime_of_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:04:11.168487+00:00
-- url     : https://prove2.me/submissions/21a5e53a-2c37-4a75-b1b4-13bf66334a9c

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    IsStoppingTime 𝓕 (twoSidedExitUpTime X b) := by
  exact MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    fun i => AvramDividend.Classical.levy_upperPassage_lt_filtration_measurable X b i
