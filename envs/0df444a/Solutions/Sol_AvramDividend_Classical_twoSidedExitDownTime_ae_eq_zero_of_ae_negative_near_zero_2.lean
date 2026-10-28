-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitDownTime_ae_eq_zero_of_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:04:12.005994+00:00
-- url     : https://prove2.me/submissions/e3b68588-41e2-4608-b388-0631a4b4c099

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_near_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0 := by 
  filter_upwards [hnear] with ω hω
  exact twoSidedExitDownTime_eq_zero_of_negative_near_zero X ω hω
