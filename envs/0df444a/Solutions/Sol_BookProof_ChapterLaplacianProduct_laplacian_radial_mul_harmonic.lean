-- Prove2me | solution 1 for BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:31:54.594822+00:00
-- url     : https://prove2.me/submissions/4ef7888b-65d4-4daa-9a88-2290093d77c0

import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterLaplacianProduct_laplacian_mul
import Theorems.Thm_BookProof_ChapterLaplacianProduct_sum_inner_mul_apply
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_sum_inner_sq
import Theorems.Thm_BookProof_ChapterRadialLaplacian_diffAt_deriv_of_contDiffAt_two
-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem h44_hasFDerivAt_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) ((1 / ‖x‖) • innerCLM E x) x := by
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hne : ‖x‖ ^ 2 ≠ 0 := by positivity
  have h := h2.sqrt hne
  have hf : (fun y : E => Real.sqrt (‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  rw [hf] at h
  refine h.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, Real.sqrt_sq (norm_nonneg x)]
  rw [show innerCLM E x w = ⟪x, w⟫_ℝ from rfl]
  simp only [smul_eq_mul, nsmul_eq_mul]
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp
  ring

theorem h44_hasFDerivAt_radial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : ℝ → ℝ} {x : E}
    (hx : x ≠ 0) (hd : DifferentiableAt ℝ g ‖x‖) :
    HasFDerivAt (fun y : E => g ‖y‖) ((deriv g ‖x‖ / ‖x‖) • innerCLM E x) x := by
  have h := hd.hasDerivAt.comp_hasFDerivAt x (h44_hasFDerivAt_norm hx)
  refine h.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem h44_laplacian_radial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) :
    (Δ fun y : E => g ‖y‖) x
      = deriv (deriv g) ‖x‖ + (((Module.finrank ℝ E : ℝ) - 1) / ‖x‖) * deriv g ‖x‖ := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  -- eventual formula for the first derivative
  have hev : (fderiv ℝ fun y : E => g ‖y‖) =ᶠ[nhds x]
      fun y => (deriv g ‖y‖ / ‖y‖) • innerCLM E y := by
    have h1 : ∀ᶠ y in nhds x, y ≠ 0 := isOpen_ne.mem_nhds hx
    have h2 : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 g ‖y‖ :=
      (continuous_norm.continuousAt (x := x)).eventually (hg.eventually (by simp))
    filter_upwards [h1, h2] with y hy hgy
    exact (h44_hasFDerivAt_radial hy (hgy.differentiableAt (by norm_num))).fderiv
  have hφ : HasDerivAt (fun r => deriv g r / r)
      ((deriv (deriv g) ‖x‖ * ‖x‖ - deriv g ‖x‖ * 1) / ‖x‖ ^ 2) ‖x‖ :=
    (BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two hg).hasDerivAt.div (hasDerivAt_id _) hr
  have hc := hφ.comp_hasFDerivAt x (h44_hasFDerivAt_norm hx)
  have hF := hc.smul (innerCLM E).hasFDerivAt
  have h2 : fderiv ℝ (fderiv ℝ fun y : E => g ‖y‖) x = _ := hev.fderiv_eq.trans hF.fderiv
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, Function.comp_apply]
  have hterm : ∀ i, deriv g ‖x‖ / ‖x‖ * (innerCLM E ((stdOrthonormalBasis ℝ E) i)) ((stdOrthonormalBasis ℝ E) i) +
        (deriv (deriv g) ‖x‖ * ‖x‖ - deriv g ‖x‖ * 1) / ‖x‖ ^ 2 *
            (1 / ‖x‖ * (innerCLM E x) ((stdOrthonormalBasis ℝ E) i)) *
          (innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
      = deriv g ‖x‖ / ‖x‖ + ((deriv (deriv g) ‖x‖ * ‖x‖ - deriv g ‖x‖) / ‖x‖ ^ 3)
          * ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ ^ 2 := by
    intro i
    rw [show innerCLM E ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)
        = ⟪(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl,
      real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ E).orthonormal.1 i,
      show innerCLM E x ((stdOrthonormalBasis ℝ E) i) = ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl]
    field_simp
  simp only [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, BookProof.ChapterSolidHarmonicTools.sum_inner_sq x]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem solution [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E}
    {l : ℕ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) (hH : ContDiffAt ℝ 2 H x)
    (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) :
    (Δ fun y : E => g ‖y‖ * H y) x
      = (deriv (deriv g) ‖x‖
          + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖) * deriv g ‖x‖) * H x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hgn : ContDiffAt ℝ 2 (fun y : E => g ‖y‖) x := hg.comp x (contDiffAt_norm ℝ hx)
  rw [BookProof.ChapterLaplacianProduct.laplacian_mul hgn hH, hharm, h44_laplacian_radial hx hg,
    (h44_hasFDerivAt_radial hx (hg.differentiableAt (by norm_num))).fderiv]
  have hs : ∑ i, ((deriv g ‖x‖ / ‖x‖) • innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
      * fderiv ℝ H x ((stdOrthonormalBasis ℝ E) i) = (deriv g ‖x‖ / ‖x‖) * fderiv ℝ H x x := by
    rw [← BookProof.ChapterLaplacianProduct.sum_inner_mul_apply (fderiv ℝ H x) x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show innerCLM E x ((stdOrthonormalBasis ℝ E) i) = ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl]
    ring
  rw [hs, heuler]
  field_simp
  ring

