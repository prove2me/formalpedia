-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:48:55.623787+00:00
-- url     : https://prove2.me/submissions/01df3fda-e5ae-4ab7-8ed6-7f3b7d171e66

import Mathlib
import Definitions.Def_ChapterRadialLaplacian
-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.hasFDerivAt_normSq
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


theorem solution (x : E) :
    HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℝ) • innerCLM E x) x := by
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  refine h2.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [show innerCLM E x w = ⟪x, w⟫_ℝ from rfl]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

