-- Prove2me | solution 2 for BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:56:55.27528+00:00
-- url     : https://prove2.me/submissions/dffb0dc3-72a2-472a-888f-bda6a62d9687

import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterSphericalBessel
import Theorems.Thm_BookProof_ChapterLaplacianProduct_laplacian_mul
import Theorems.Thm_BookProof_ChapterLaplacianProduct_sum_inner_mul_apply
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_sum_inner_sq
import Theorems.Thm_BookProof_ChapterRadialLaplacian_diffAt_deriv_of_contDiffAt_two
-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean
open BookProof.ChapterSphericalBessel
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
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

theorem h45_sb0_eq (p : ℝ) : (fun r => BookProof.ChapterSphericalBessel.sbessel 0 (p * r))
    = fun r => Real.sin (p * r) / (p * r) := by
  funext r
  simp [BookProof.ChapterSphericalBessel.sbessel, BookProof.ChapterSphericalBessel.sbesselBase]

theorem h45_sb0_hasDerivAt {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun r => Real.sin (p * r) / (p * r))
      (Real.cos (p * r) / r - Real.sin (p * r) / (p * r ^ 2)) r := by
  have h1 : HasDerivAt (fun r => p * r) p r := by simpa using (hasDerivAt_id r).const_mul p
  have h2 := (h1.sin).div h1 (mul_ne_zero hp hr)
  refine h2.congr_deriv ?_
  field_simp

theorem h45_sb0_hasDerivAt2 {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun r => Real.cos (p * r) / r - Real.sin (p * r) / (p * r ^ 2))
      (-(p * Real.sin (p * r)) / r - 2 * Real.cos (p * r) / r ^ 2 + 2 * Real.sin (p * r) / (p * r ^ 3)) r := by
  have h1 : HasDerivAt (fun r => p * r) p r := by simpa using (hasDerivAt_id r).const_mul p
  have hq : HasDerivAt (fun r => p * r ^ 2) (p * (2 * r)) r := by
    simpa using (hasDerivAt_pow 2 r).const_mul p
  have ha := (h1.cos).div (hasDerivAt_id r) hr
  have hb := (h1.sin).div hq (by positivity)
  refine (ha.sub hb).congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem h45_laplacian_sb0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (h3 : Module.finrank ℝ E = 3) {p : ℝ} {x : E} (hp : p ≠ 0) (hx : x ≠ 0) :
    (Laplacian.laplacian fun y : E => BookProof.ChapterSphericalBessel.sbessel 0 (p * ‖y‖)) x
      = -(p ^ 2) * BookProof.ChapterSphericalBessel.sbessel 0 (p * ‖x‖) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hg : ContDiffAt ℝ 2 (fun r => Real.sin (p * r) / (p * r)) ‖x‖ := by
    apply ContDiffAt.div
    · exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffAt
    · exact (contDiff_const.mul contDiff_id).contDiffAt
    · exact mul_ne_zero hp hr
  have key := h44_laplacian_radial hx hg
  have hf : (fun y : E => BookProof.ChapterSphericalBessel.sbessel 0 (p * ‖y‖))
      = fun y : E => (fun r => Real.sin (p * r) / (p * r)) ‖y‖ := by
    funext y; exact congrFun (h45_sb0_eq p) ‖y‖
  have hd1 : deriv (fun r => Real.sin (p * r) / (p * r)) ‖x‖
      = Real.cos (p * ‖x‖) / ‖x‖ - Real.sin (p * ‖x‖) / (p * ‖x‖ ^ 2) := (h45_sb0_hasDerivAt hp hr).deriv
  have hev : deriv (fun r => Real.sin (p * r) / (p * r)) =ᶠ[nhds ‖x‖]
      fun r => Real.cos (p * r) / r - Real.sin (p * r) / (p * r ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hr] with r hr'
    exact (h45_sb0_hasDerivAt hp hr').deriv
  have hd2 : deriv (deriv (fun r => Real.sin (p * r) / (p * r))) ‖x‖
      = -(p * Real.sin (p * ‖x‖)) / ‖x‖ - 2 * Real.cos (p * ‖x‖) / ‖x‖ ^ 2
          + 2 * Real.sin (p * ‖x‖) / (p * ‖x‖ ^ 3) := by
    rw [hev.deriv_eq]; exact (h45_sb0_hasDerivAt2 hp hr).deriv
  rw [hf, key, hd1, hd2, h3, congrFun (h45_sb0_eq p) ‖x‖]
  field_simp
  ring

theorem solution {p : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : EuclideanSpace ℝ (Fin 3) => sbessel 0 (p * ‖y‖)) x
      = p ^ 2 * sbessel 0 (p * ‖x‖) := by
  rw [h45_laplacian_sb0 (by simp) hp hx]
  ring

