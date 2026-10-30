-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_06_gaussian_residual_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:26:47.766991+00:00
-- url     : https://prove2.me/submissions/e1116678-15c5-4142-9ab3-5bce10da2364

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_weighted_residual_three_gaps
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_sigma_pos
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- The only global Gaussian input is weighted second derivative and jump
    integrability with genuine Fubini, uniformly in the Laplace parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hD2 : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hJ : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
        (Ioi (0 : ℝ)))
    (hF : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * (X.generator W x - q * W x))
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiffOn_two_of_sigma_pos X hX q hq W hW hσ
  have hC1 : ContDiffOn ℝ 1 (deriv W) (Ioi (0 : ℝ)) :=
    hC2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hDeriv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt W (deriv W x) x := by
    intro x hx
    exact ((hC2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hDeriv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x := by
    intro x hx
    exact ((hC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hZero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hRight : Tendsto (deriv W) (𝓝[>] (0 : ℝ))
      (𝓝 (2 / X.σ ^ 2)) :=
    scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
      X q hq W hW hσ hZero hDeriv
  have hIter : (iteratedDeriv 2 W) = deriv (deriv W) := by
    funext x
    simp [iteratedDeriv_eq_iterate, Function.iterate_succ, Function.iterate_zero]
  intro θ hθ hqθ
  have hi2 := (hD2 θ hθ hqθ).const_mul (X.σ ^ 2 / 2)
  have hi1 := (chat07_scale_weighted_deriv_integrable_positive_halfline
    X q W hW θ hθ hqθ).const_mul X.c
  have hiW := ((hW.2.2.2.2 θ hθ hqθ).1).const_mul q
  have hi := ((hi2.add hi1).add (hJ θ hθ hqθ)).sub hiW
  have hInt : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * (X.generator W x - q * W x))
      (Ioi (0 : ℝ)) := by
    apply hi.congr
    filter_upwards with x
    simp only [SpectrallyNegativeLevy.generator, hIter, Pi.add_apply, Pi.sub_apply]
    ring
  refine ⟨hInt, ?_⟩
  have hz := avram_root29_06_gaussian_weighted_residual_three_gaps
    X q hq W hW hσ θ (2 / X.σ ^ 2) hθ hqθ
    hDeriv hRight hDeriv1 (hD2 θ hθ hqθ)
    (hJ θ hθ hqθ) (hF θ hθ hqθ)
  simpa only [SpectrallyNegativeLevy.generator, hIter] using hz
