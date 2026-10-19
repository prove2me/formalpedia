-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:18:18.900572+00:00
-- url     : https://prove2.me/submissions/6737cbff-2cc5-4d92-9844-b79e1824e025

import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterRadialLaplacian
-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


theorem solution (e : E) (j m : ℕ) (x : E) :
    HasFDerivAt (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m)
      (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e
        + (2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x) x := by
  have h1 : HasFDerivAt (fun y : E => ⟪e, y⟫_ℝ) (innerCLM E e) x := (innerCLM E e).hasFDerivAt
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := ((h1.pow j).fun_mul (h2.pow m))
  refine h.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_add', Pi.smul_apply, Pi.add_apply,
    innerSL_apply_apply]
  show _ = (j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m * ⟪e, w⟫_ℝ + 2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1) * ⟪x, w⟫_ℝ
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [show innerCLM E e w = ⟪e, w⟫_ℝ from rfl]
  ring

