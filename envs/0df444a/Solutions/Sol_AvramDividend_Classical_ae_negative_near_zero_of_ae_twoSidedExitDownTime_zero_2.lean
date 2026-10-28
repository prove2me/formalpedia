-- Prove2me | solution 2 for AvramDividend.Classical.ae_negative_near_zero_of_ae_twoSidedExitDownTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:17:25.054826+00:00
-- url     : https://prove2.me/submissions/7a360763-b73f-4062-9db3-392098b96910

import Theorems.Thm_AvramDividend_Classical_negative_near_zero_of_twoSidedExitDownTime_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Almost-sure instantaneous exit gives almost-sure near-zero strict crossings. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h0 : ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by
  exact h0.mono (fun ω hω =>
    negative_near_zero_of_twoSidedExitDownTime_zero X ω hω)
