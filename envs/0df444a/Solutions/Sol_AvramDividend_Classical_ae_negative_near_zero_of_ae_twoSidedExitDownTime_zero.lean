-- Prove2me | solution 1 for AvramDividend.Classical.ae_negative_near_zero_of_ae_twoSidedExitDownTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:17:16.009547+00:00
-- url     : https://prove2.me/submissions/55e25a64-e1a7-453f-81ed-30267abf9b49

import Theorems.Thm_AvramDividend_Classical_negative_near_zero_of_twoSidedExitDownTime_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h0 : ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by 
  filter_upwards [h0] with ω hω
  exact negative_near_zero_of_twoSidedExitDownTime_zero X ω hω
