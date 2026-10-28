-- Prove2me | solution 1 for AvramDividend.Classical.psi_normalised_unbounded_of_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:26:09.364164+00:00
-- url     : https://prove2.me/submissions/897ef5f1-571f-44a2-988b-b62be84cf1e7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_small_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Both unbounded-variation mechanisms force superlinear exponent growth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ := by
  rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv
    with hσ | hj
  · exact gaussian_psi_superlinear_of_positive_sigma X hσ
  · by_cases hσ : 0 < X.σ
    · exact gaussian_psi_superlinear_of_positive_sigma X hσ
    · have hz : X.σ = 0 :=
        le_antisymm (le_of_not_gt hσ) X.σ_nonneg
      exact psi_normalised_unbounded_small_jumps X hz hj
