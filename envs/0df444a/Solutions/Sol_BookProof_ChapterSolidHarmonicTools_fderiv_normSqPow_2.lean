-- Prove2me | solution 2 for BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:19:03.62258+00:00
-- url     : https://prove2.me/submissions/8ba3d933-e77e-474b-bd49-9eb19b755390

import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterRadialLaplacian
-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


theorem solution (m : ℕ) (x : E) :
    fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x = (2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x := by
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  refine (h2.pow m).fderiv.trans ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [show innerCLM E x w = ⟪x, w⟫_ℝ from rfl]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

