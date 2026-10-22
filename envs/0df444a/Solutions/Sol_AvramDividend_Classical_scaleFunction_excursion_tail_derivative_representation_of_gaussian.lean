-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:29:30.450723+00:00
-- url     : https://prove2.me/submissions/7db69c9f-0f1f-44e0-a878-2ab4a6f3db97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
A source-complete reduction of the Gaussian excursion-tail derivative
representation to the published unbounded-variation excursion-integral
representation. The imported excursion theorem is presently Open, so an
accepted reduction is a proof-sketch until that analytic input is proved.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    have hσzero : X.σ = 0 := hbv.1
    exact (ne_of_gt hσ) hσzero
  obtain ⟨φ, μ, hφ, hnull, hfin, hμcont, hexp⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x :=
    excursion_integral_scale_derivative W φ μ hμcont hexp
  refine ⟨φ, μ, hφ, hnull, hfin, ?_, ?_⟩
  · intro x hx
    exact (hderiv x hx).differentiableAt
  · intro x hx
    exact (hderiv x hx).deriv
