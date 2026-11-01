-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_residual_from_eventual_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:20:16.792995+00:00
-- url     : https://prove2.me/submissions/293e2a44-ca10-47ec-9543-abbe5244fa00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_weighted
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable
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
/-- The true Gaussian generator residual has a vanishing weighted transform
    for all sufficiently large admissible weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hprod : ∃ bJ : ℝ, ∀ θ : ℝ, bJ ≤ θ → 0 ≤ θ → q < X.ψ θ →
      Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod
          (X.ν.restrict (Iio (0 : ℝ))))) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0 := by
  obtain ⟨b₂, hb₂⟩ :=
    avram_wave3_05_source_gaussian_Wsecond_weighted
      X q hq W hW hσ φ hφ hroot
  obtain ⟨bJ, hbJ⟩ := hprod
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
  refine ⟨max b₂ bJ, ?_⟩
  intro θ hθb hθ hqθ
  have hD2 := hb₂ θ (le_trans (le_max_left _ _) hθb) hθ hqθ
  have hprod := hbJ θ (le_trans (le_max_right _ _) hθb) hθ hqθ
  have hJ := bv_weighted_jump_integrable_of_product_integrable X θ W hprod
  have hF := scaleFunction_generator_weighted_global_fubini_of_prod_integrable
    X W θ hprod
  have hi2 := hD2.const_mul (X.σ ^ 2 / 2)
  have hi1 := (chat07_scale_weighted_deriv_integrable_positive_halfline
    X q W hW θ hθ hqθ).const_mul X.c
  have hiW := ((hW.2.2.2.2 θ hθ hqθ).1).const_mul q
  have hi := ((hi2.add hi1).add hJ).sub hiW
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
    hDeriv hRight hDeriv1 hD2 hJ hF
  simpa only [SpectrallyNegativeLevy.generator, hIter] using hz
