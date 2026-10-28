-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:31:58.514926+00:00
-- url     : https://prove2.me/submissions/7863eea4-357b-4512-869b-791674b12223

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The strict upper-before-lower exit probability is monotone in both barriers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (alo ahi blo bhi : ℝ) (hu : alo ≤ ahi) (hd : blo ≤ bhi) :
    P {ω : Ω | twoSidedExitUpTime X ahi ω < twoSidedExitDownTime X bhi ω} ≤
      P {ω : Ω | twoSidedExitUpTime X alo ω < twoSidedExitDownTime X blo ω} := by
  exact measure_mono
    (twoSidedExitBeforeDown_event_mono_bounds X alo ahi blo bhi hu hd)
