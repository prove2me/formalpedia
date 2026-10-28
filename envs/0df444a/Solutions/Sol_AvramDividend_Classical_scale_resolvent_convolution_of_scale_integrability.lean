-- Prove2me | solution 1 for AvramDividend.Classical.scale_resolvent_convolution_of_scale_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:55:57.116865+00:00
-- url     : https://prove2.me/submissions/28b2167b-8eaf-4f5a-bd3d-591ead9f52d3

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_continuous_integrable
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_of_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Resolvent convolution for two scale functions, with regularity and
integrability supplied by their defining Laplace transforms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ b : ℝ) (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂)
    (hlarge : ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ)
    (hanchor : ∃ θ : ℝ, b < θ) :
    ∀ x : ℝ, 0 < x →
      W₂ x = W₁ x + (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := by
  obtain ⟨θ₀, hθ₀⟩ := hanchor
  obtain ⟨hθ₀nn, _, hψ₂₀⟩ := hlarge θ₀ hθ₀
  have hI₂₀ : IntegrableOn
      (fun y : ℝ => Real.exp (-(θ₀ * y)) * W₂ y) (Ioi (0 : ℝ)) :=
    (hW₂.2.2.2.2 θ₀ hθ₀nn hψ₂₀).1
  have hKcont : ContinuousOn
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s))
      (Ioi (0 : ℝ)) :=
    positive_causal_convolution_continuous_of_weighted_integrable
      W₁ W₂ θ₀ hW₁.2.2.1 hI₂₀
  have hKint : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)))
        (Ioi (0 : ℝ)) := by
    intro θ hθ
    obtain ⟨hθnn, hψ₁, hψ₂⟩ := hlarge θ hθ
    exact positive_causal_convolution_laplace_integrable W₁ W₂ θ
      (hW₁.2.2.2.2 θ hθnn hψ₁).1
      (hW₂.2.2.2.2 θ hθnn hψ₂).1
  exact scale_resolvent_convolution_of_continuous_integrable
    X q₁ q₂ b W₁ W₂ hW₁ hW₂ hlarge hKcont hKint
