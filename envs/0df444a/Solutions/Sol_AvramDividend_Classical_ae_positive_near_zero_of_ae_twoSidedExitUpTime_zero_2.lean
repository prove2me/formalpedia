-- Prove2me | solution 2 for AvramDividend.Classical.ae_positive_near_zero_of_ae_twoSidedExitUpTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:17:28.50596+00:00
-- url     : https://prove2.me/submissions/6d66a151-ed74-4933-821a-34f20edcc62f

import Theorems.Thm_AvramDividend_Classical_positive_near_zero_of_twoSidedExitUpTime_zero
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
    (h0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω := by
  exact h0.mono (fun ω hω =>
    positive_near_zero_of_twoSidedExitUpTime_zero X ω hω)
