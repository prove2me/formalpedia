-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p2_original_laplace_slope_bounded_below_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:37:48.382245+00:00
-- url     : https://prove2.me/submissions/5b377149-95f4-4046-8627-04190989fd4c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18p2a_original_standing_jensen_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Jensen estimate provides a finite real lower bound for every small positive Laplace slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) :
    ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      -C ≤ laplaceExponent X.c X.σ X.ν θ / θ := by
  refine ⟨-(∫ ω, X.X 1 ω ∂P), ?_⟩
  intro θ hθ hθOne
  have hJensen :=
    avram_ja18p2a_original_standing_jensen_psi X hX θ hθ hθOne
  apply (le_div_iff₀ hθ).2
  simpa only [neg_neg, mul_comm] using hJensen
