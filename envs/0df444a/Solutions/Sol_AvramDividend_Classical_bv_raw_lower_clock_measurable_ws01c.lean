-- Prove2me | solution 1 for AvramDividend.Classical.bv_raw_lower_clock_measurable_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:00:56.540994+00:00
-- url     : https://prove2.me/submissions/e937bf9c-5c3f-4add-8c28-6b55365e61b0

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_named_lower_passage_lt_horizon_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_ennreal_measurable_of_finite_strict_sublevels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (lower : ℝ) :
    Measurable (twoSidedExitDownTime X lower) := by
  apply chat03_ennreal_measurable_of_finite_strict_sublevels
  intro T
  exact chat03_named_lower_passage_lt_horizon_measurable X lower T
