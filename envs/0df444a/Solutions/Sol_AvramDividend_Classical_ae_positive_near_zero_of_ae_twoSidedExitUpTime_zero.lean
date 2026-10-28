-- Prove2me | solution 1 for AvramDividend.Classical.ae_positive_near_zero_of_ae_twoSidedExitUpTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:17:16.559594+00:00
-- url     : https://prove2.me/submissions/b151ce63-f9f7-4a3e-9767-107d32555eb5

import Theorems.Thm_AvramDividend_Classical_positive_near_zero_of_twoSidedExitUpTime_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω := by 
  filter_upwards [h0] with ω hω
  exact positive_near_zero_of_twoSidedExitUpTime_zero X ω hω
