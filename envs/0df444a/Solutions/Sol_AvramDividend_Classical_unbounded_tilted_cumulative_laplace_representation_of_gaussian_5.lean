-- Prove2me | solution 5 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:39:38.153192+00:00
-- url     : https://prove2.me/submissions/a6ba9a5c-68e4-4284-8b31-ee8bb233a781

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_cumulative_laplace_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    exact (ne_of_gt hσ) hbv.1
  exact unbounded_tilted_cumulative_laplace_representation
    X hX q hq W hW hnbv
