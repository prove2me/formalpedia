-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_bv_ac
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:34:05.34998+00:00
-- url     : https://prove2.me/submissions/9f522388-92de-4e9b-92c7-616e503f57f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative

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
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x → deriv W x = W x * (φ + μ.real (Ici x))) := by
  obtain ⟨φ, μ, hφ, hnull, hfinite, hcont, hexp⟩ :=
    AvramDividend.Classical.bv_ac_esscher_excursion_integrated_scale_representation
      X hX q hq W hW hbv hac
  have hderiv :
      ∀ x : ℝ, 0 < x →
        HasDerivAt W (W x * (φ + μ.real (Ici x))) x :=
    AvramDividend.Classical.excursion_integral_scale_derivative W φ μ hcont hexp
  refine ⟨φ, μ, hφ, hnull, hfinite, ?_, ?_⟩
  · intro x hx
    exact (hderiv x hx).differentiableAt
  · intro x hx
    exact (hderiv x hx).deriv
