-- Prove2me | solution 1 for AvramDividend.Classical.upperPassage_stopping_rightCont_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:52:39.647039+00:00
-- url     : https://prove2.me/submissions/8de7fe2e-cfc9-4153-a9ab-8961f436b02e

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    IsStoppingTime 𝓕.rightCont (twoSidedExitUpTime X b) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  exact (𝓕.le_rightCont t) _
    (levy_upperPassage_lt_filtration_measurable X b t)
