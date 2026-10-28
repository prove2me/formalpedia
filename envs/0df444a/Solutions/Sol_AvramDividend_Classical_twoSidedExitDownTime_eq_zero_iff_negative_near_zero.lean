-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_eq_zero_iff_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:19:35.873307+00:00
-- url     : https://prove2.me/submissions/f1be9211-f3fb-45da-8ca2-d0ace7457c4f

import Theorems.Thm_AvramDividend_Classical_negative_near_zero_of_twoSidedExitDownTime_zero
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_near_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero-time strict exit is equivalent to arbitrary near-zero strict crossings. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    twoSidedExitDownTime X 0 ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by
  constructor
  · exact negative_near_zero_of_twoSidedExitDownTime_zero X ω
  · exact twoSidedExitDownTime_eq_zero_of_negative_near_zero X ω
