-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitUpTime_ae_eq_zero_of_ae_positive_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:08:44.884389+00:00
-- url     : https://prove2.me/submissions/2c78223a-2776-4a1d-b86e-c339ec0b701e

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_near_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Almost-sure positive observations near zero imply instantaneous upper exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0 := by
  exact hnear.mono (fun ω hω =>
    twoSidedExitUpTime_eq_zero_of_positive_near_zero X ω hω)
