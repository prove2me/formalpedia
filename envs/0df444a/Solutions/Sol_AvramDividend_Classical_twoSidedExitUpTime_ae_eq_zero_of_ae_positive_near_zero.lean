-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitUpTime_ae_eq_zero_of_ae_positive_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:07:27.551501+00:00
-- url     : https://prove2.me/submissions/0e427a53-fb34-47ee-bf52-2bbbc48415e7

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_near_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0 := by 
  filter_upwards [hnear] with ω hω
  exact twoSidedExitUpTime_eq_zero_of_positive_near_zero X ω hω
