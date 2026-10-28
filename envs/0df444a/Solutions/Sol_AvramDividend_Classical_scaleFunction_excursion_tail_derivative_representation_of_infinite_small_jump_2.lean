-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:09:30.286347+00:00
-- url     : https://prove2.me/submissions/46ad7131-e1c4-477a-bab4-c934b4e29d43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
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
    intro hBV
    have hInt :=
      AvramDividend.Classical.bv_small_negative_first_moment_integrable X hBV
    have hAbs : IntegrableOn (fun y : ℝ => |y|) (Ioo (-1 : ℝ) 0) X.ν := by
      have hEq : (fun y : ℝ => -y) =ᵐ[X.ν.restrict (Ioo (-1 : ℝ) 0)] (fun y : ℝ => |y|) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with y hy
        simp only [Set.mem_Ioo] at hy
        exact (abs_of_neg hy.2).symm
      exact hInt.congr hEq
    have hpos : ∀ᵐ y ∂ (X.ν.restrict (Ioo (-1 : ℝ) 0)), 0 ≤ |y| :=
      Eventually.of_forall fun y => abs_nonneg _
    have hFin : HasFiniteIntegral (fun y : ℝ => |y|) (X.ν.restrict (Ioo (-1 : ℝ) 0)) :=
      hAbs.hasFiniteIntegral
    have hlt : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ :=
      (MeasureTheory.hasFiniteIntegral_iff_ofReal hpos).mp hFin
    rw [hvar] at hlt
    exact (lt_irrefl _ hlt).elim
  obtain ⟨φ, μ, hφ, hnull, hfin, hcont, hexp⟩ :=
    AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  have hderiv :=
    AvramDividend.Classical.excursion_integral_scale_derivative W φ μ hcont hexp
  refine ⟨φ, μ, hφ, hnull, hfin, ?_, ?_⟩
  · intro x hx
    exact (hderiv x hx).differentiableAt
  · intro x hx
    exact (hderiv x hx).deriv
