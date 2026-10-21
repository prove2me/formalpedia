-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_named_exit_lt_horizon_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:09:04.537123+00:00
-- url     : https://prove2.me/submissions/520789c9-ea2d-4265-a230-32f1165a45d0

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_named_upper_passage_lt_horizon_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_named_lower_passage_lt_horizon_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The minimum of the two exact named strict passage times has
measurable strict sublevel events at every finite horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | min (twoSidedExitUpTime X upper ω)
        (twoSidedExitDownTime X lower ω) < (T : ℝ≥0∞)} := by
  have hUp :=
    chat03_named_upper_passage_lt_horizon_measurable X upper T
  have hDown :=
    chat03_named_lower_passage_lt_horizon_measurable X lower T
  have hUnion : MeasurableSet
      ({ω : Ω | twoSidedExitUpTime X upper ω < (T : ℝ≥0∞)} ∪
       {ω : Ω | twoSidedExitDownTime X lower ω < (T : ℝ≥0∞)}) :=
    hUp.union hDown
  simpa only [Set.setOf_or, min_lt_iff] using hUnion
