-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.radialFactor_euler
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:37:32.49112+00:00
-- url     : https://prove2.me/submissions/f9a12c08-d75b-493d-9c36-59ceb80e59d5

import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterLegendrePolynomial
import Definitions.Def_ChapterRadialLaplacian
-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.radialFactor_euler
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

theorem h43_hasFDerivAt_radialFactor (e : E) (l μ : ℕ) (x : E) :
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

theorem h43_pow_pred_mul (z : ℝ) (j : ℕ) : (j : ℝ) * z ^ (j - 1) * z = j * z ^ j := by
  rcases j with _ | j
  · simp
  · simp [pow_succ]; ring

theorem h43_radialFactor_euler (e : E) (l μ : ℕ) (x : E) :
    fderiv ℝ (radialFactor e l μ) x x = ((l - μ : ℕ) : ℝ) * radialFactor e l μ x := by
  rw [(h43_hasFDerivAt_radialFactor e l μ x).fderiv, radialFactor, Finset.mul_sum,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : 2 * m ≤ l - μ := by
    have := Finset.mem_range.mp hm; omega
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_add', Pi.smul_apply, Pi.add_apply,
    h43_innerCLM_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
  have e1 := h43_pow_pred_mul (⟪e, x⟫_ℝ) (l - μ - 2 * m)
  have e2 := h43_pow_pred_mul (‖x‖ ^ 2) m
  have hc : (((l - μ - 2 * m : ℕ) : ℝ)) = ((l - μ : ℕ) : ℝ) - 2 * m := by
    rw [Nat.cast_sub hm']; push_cast; ring
  calc _ = (derivative^[μ] (legendre l)).coeff (l - μ - 2 * m) *
        (((l - μ - 2 * m : ℕ) : ℝ) * ⟪e, x⟫_ℝ ^ (l - μ - 2 * m - 1) * ⟪e, x⟫_ℝ * (‖x‖ ^ 2) ^ m
          + 2 * (⟪e, x⟫_ℝ ^ (l - μ - 2 * m)) * ((m : ℝ) * (‖x‖ ^ 2) ^ (m - 1) * ‖x‖ ^ 2)) := by ring
    _ = _ := by rw [e1, e2, hc]; ring

theorem solution (e : E) (l μ : ℕ) (x : E) :
    fderiv ℝ (radialFactor e l μ) x x = ((l - μ : ℕ) : ℝ) * radialFactor e l μ x := by
  exact h43_radialFactor_euler e l μ x

