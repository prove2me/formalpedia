-- Prove2me | solution 2 for BookProof.ChapterLaplacianProduct.fderiv_radial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:27:47.253999+00:00
-- url     : https://prove2.me/submissions/e75b98e0-9227-4db2-a08f-a6d82f7e514b

import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.fderiv_radial
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

theorem solution {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) :
    fderiv ℝ (fun y : E => g ‖y‖) x = (deriv g ‖x‖ / ‖x‖) • innerCLM E x := by
  have hd : DifferentiableAt ℝ g ‖x‖ := hg.differentiableAt (by norm_num)
  have h := hd.hasDerivAt.comp_hasFDerivAt x (h44_hasFDerivAt_norm hx)
  refine h.fderiv.trans ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

