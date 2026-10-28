-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_ae_eq_zero_of_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:03:14.709563+00:00
-- url     : https://prove2.me/submissions/4dc8ae70-57f6-41be-8822-acbe78c7de78

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_near_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Almost-sure negative observations near zero imply instantaneous lower exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0 := by
  exact hnear.mono (fun ω hω =>
    twoSidedExitDownTime_eq_zero_of_negative_near_zero X ω hω)
