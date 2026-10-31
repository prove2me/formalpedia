-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_unbounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:57:47.75459+00:00
-- url     : https://prove2.me/submissions/417b96aa-9f4f-4b92-9442-ab308215945f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Differentiate the genuine unbounded Esscher excursion integral formula. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by
  obtain ⟨φ, μ, hφ, hnull, hfinite, hcont, hrepr⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hbv
  refine ⟨φ, μ, hφ, hnull, hfinite, ?_, ?_⟩
  · intro x hx
    exact (excursion_integral_scale_derivative
      W φ μ hcont hrepr x hx).differentiableAt
  · intro x hx
    exact (excursion_integral_scale_derivative
      W φ μ hcont hrepr x hx).deriv
