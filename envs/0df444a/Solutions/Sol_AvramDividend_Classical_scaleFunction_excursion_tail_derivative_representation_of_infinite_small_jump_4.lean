-- Prove2me | solution 4 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:25:57.118402+00:00
-- url     : https://prove2.me/submissions/928a3583-f3b9-479b-a738-7b29a62252d2
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

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
        {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (q : ℝ) (hq : 0 < q)
        (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    have hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) < ⊤ := hbv.2
    rw [hvar] at hsmall
    exact lt_irrefl _ hsmall
  obtain ⟨φ, μ, hφ, hnull, hfin, hcont, hexp⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x :=
    excursion_integral_scale_derivative W φ μ hcont hexp
  exact ⟨φ, μ, hφ, hnull, hfin,
    fun x hx => (hderiv x hx).differentiableAt,
    fun x hx => (hderiv x hx).deriv⟩
