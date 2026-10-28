-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:33:08.638432+00:00
-- url     : https://prove2.me/submissions/0de0d30a-3b9d-4663-918b-92aec0342f8c

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
import Mathlib.MeasureTheory.OuterMeasure.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (alo ahi blo bhi : ℝ) (hu : alo ≤ ahi) (hd : blo ≤ bhi) :
    P {ω : Ω | twoSidedExitUpTime X ahi ω < twoSidedExitDownTime X bhi ω} ≤
      P {ω : Ω | twoSidedExitUpTime X alo ω < twoSidedExitDownTime X blo ω} :=
  measure_mono (twoSidedExitBeforeDown_event_mono_bounds X alo ahi blo bhi hu hd)