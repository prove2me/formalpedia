-- Prove2me | solution 2 for BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:35:09.133992+00:00
-- url     : https://prove2.me/submissions/d91167e3-7dea-4114-9892-c8e6860e49af

import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterLegendrePolynomial
import Definitions.Def_ChapterRadialLaplacian
-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor
open BookProof.ChapterLegendrePolynomial
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem h43_innerCLM_apply (a b : E) : innerCLM E a b = ⟪a, b⟫_ℝ := rfl

theorem h43_term_hasFDerivAt (e x : E) (c : ℝ) (j m : ℕ) :
    HasFDerivAt (fun y : E => c * ((⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m))
      (c • (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e
            + (2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x)) x := by
  have h1 : HasFDerivAt (fun y : E => ⟪e, y⟫_ℝ) (innerCLM E e) x := (innerCLM E e).hasFDerivAt
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := ((h1.pow j).fun_mul (h2.pow m)).const_mul c
  refine h.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_add', Pi.smul_apply, Pi.add_apply,
    h43_innerCLM_apply, innerSL_apply_apply]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem solution (e : E) (l μ : ℕ) (x : E) :
    HasFDerivAt (radialFactor e l μ)
      (∑ m ∈ Finset.range ((l - μ) / 2 + 1),
        ((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)) •
          ((((l - μ - 2 * m : ℕ) : ℝ) * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m - 1) * (‖x‖ ^ 2) ^ m)
              • innerCLM E e
            + (2 * m * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m) * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x)) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.range ((l - μ) / 2 + 1)) (fun m _ =>
    h43_term_hasFDerivAt e x ((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)) (l - μ - 2 * m) m)
  refine h.congr_fderiv ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rfl

