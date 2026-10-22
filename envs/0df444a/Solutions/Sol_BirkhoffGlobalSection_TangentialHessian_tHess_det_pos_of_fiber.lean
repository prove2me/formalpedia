-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.tHess_det_pos_of_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:28.404103+00:00
-- url     : https://prove2.me/submissions/abbd46c0-6976-4e53-afd6-7a8b20cc656f

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Theorems.Thm_det_quaternionFrame_eq_bordered
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_poly_pos
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_derivative_pos_of_reduced
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_kHessR_transpose
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_K_eq_fiber
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_bordered_pos_of_fiber
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHessR_frame
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

namespace BirkhoffGlobalSection.TangentialHessian.ReductionDAux

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian

/-- `radrR2 = r · F` (the (C) quantity `R² r` is our fiber radius squared times `r`). -/
theorem radrR2_eq (μ c r : ℝ) (s : Phase) (hr : r ≠ 0) :
    radrR2 μ c (zNormSq s) (uCoord s) r = r * fibF μ c r s := by
  simp only [radrR2, fibF, zNormSq, uCoord]
  field_simp
  ring

/-- A vector with `0 < s · g` for some `s` has `0 < g · g`. -/
theorem dot_self_pos_of_sum (s g : Fin 4 → ℝ) (h : 0 < ∑ i, s i * g i) : 0 < g ⬝ᵥ g := by
  have hne : ∃ i, g i ≠ 0 := by
    by_contra hall
    push Not at hall
    simp [hall] at h
  obtain ⟨i, hi⟩ := hne
  have h1 : 0 < g i * g i := mul_self_pos.mpr hi
  have h2 : g i * g i ≤ ∑ j, g j * g j :=
    Finset.single_le_sum (f := fun j => g j * g j) (fun j _ => mul_self_nonneg (g j))
      (Finset.mem_univ i)
  simpa [dotProduct] using lt_of_lt_of_le h1 h2

end BirkhoffGlobalSection.TangentialHessian.ReductionDAux

open Matrix in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.ReductionDAux in
theorem solution (μ c r : ℝ) (s : Phase)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hz : 2 * zNormSq s ≤ (3 - 2 * μ) / 5)
    (hG : 0 < fibG μ c r s)
    (hW : fibF μ c r s * (fibBeta1 μ c r s ^ 2 + fibBeta2 μ c r s ^ 2) < fibG μ c r s ^ 2) :
    0 < (tHessR μ c r s).det := by
  -- (C) chain: s · ∇K > 0, hence ∇K ≠ 0
  have hc : kGradR μ c r s 2 ^ 2 + kGradR μ c r s 3 ^ 2 = fibF μ c r s := by
    have := K_eq_fiber μ c r s; linarith
  have hF0 : 0 ≤ fibF μ c r s := by rw [← hc]; positivity
  have hZ0 : 0 ≤ zNormSq s := by unfold zNormSq; positivity
  have hu1 : uCoord s ≤ zNormSq s := by unfold uCoord zNormSq; nlinarith [sq_nonneg (s 1)]
  have hu2 : -zNormSq s ≤ uCoord s := by unfold uCoord zNormSq; nlinarith [sq_nonneg (s 0)]
  have hr2' : r ^ 2 = 4 * zNormSq s ^ 2 - 4 * uCoord s + 1 := by
    rw [hr2]; unfold secondCollisionDistanceSq zNormSq uCoord; ring
  have hR : 0 ≤ radrR2 μ c (zNormSq s) (uCoord s) r := by
    rw [radrR2_eq μ c r s hr.ne']; positivity
  have hpoly := radial_poly_pos μ c (zNormSq s) (uCoord s) r hμ0 hμhalf hc0 hc1 hZ0 hz hu1 hu2 hr hr2' hR
  have hsg := radial_derivative_pos_of_reduced μ c r s hr hK hpoly
  have hg2 : 0 < kGradR μ c r s ⬝ᵥ kGradR μ c r s := dot_self_pos_of_sum s _ hsg
  -- (D): det = |g|⁴ · B and B > 0 on the fiber
  have hsym : ∀ i j, kHessR μ c r s i j = kHessR μ c r s j i := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (kHessR_transpose μ c r s) j) i
  have hHm : (!![kHessR μ c r s 0 0, kHessR μ c r s 0 1, kHessR μ c r s 0 2, kHessR μ c r s 0 3;
        kHessR μ c r s 0 1, kHessR μ c r s 1 1, kHessR μ c r s 1 2, kHessR μ c r s 1 3;
        kHessR μ c r s 0 2, kHessR μ c r s 1 2, kHessR μ c r s 2 2, kHessR μ c r s 2 3;
        kHessR μ c r s 0 3, kHessR μ c r s 1 3, kHessR μ c r s 2 3, kHessR μ c r s 3 3] :
          Matrix (Fin 4) (Fin 4) ℝ) = kHessR μ c r s := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1, hsym 3 2]
  have hgv : ![kGradR μ c r s 0, kGradR μ c r s 1, kGradR μ c r s 2, kGradR μ c r s 3] =
      kGradR μ c r s := by
    ext i; fin_cases i <;> rfl
  rw [tHessR_frame, det_quaternionFrame_eq_bordered, hHm, hgv]
  exact mul_pos (pow_pos hg2 2) (bordered_pos_of_fiber μ c r s hK hG hW)
