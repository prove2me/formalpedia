-- Prove2me | solution 1 for EllipsoidGLS.Rounded.inv_Astar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:47:16.998189+00:00
-- url     : https://prove2.me/submissions/54aa9589-859e-4f75-b4cd-334e49f1122d

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

open Matrix EllipsoidGLS.Rounded

theorem solution {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (Astar A a).PosDef ∧
      (Astar A a)⁻¹ = (2 * (n : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2 + 3)) •
        (A⁻¹ + ((2 / ((n : ℝ) - 1)) * (a ⬝ᵥ A.mulVec a)⁻¹) • vecMulVec a a) := by
  set q := a ⬝ᵥ A.mulVec a with hq
  have hqpos : 0 < q := by
    have := hA.dotProduct_mulVec_pos ha
    simpa using this
  have hAT : Aᵀ = A := by
    have h := hA.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hunit : IsUnit A := hA.isUnit
  have hAinv : A * A⁻¹ = 1 := mul_nonsing_inv A ((isUnit_iff_isUnit_det A).1 hunit)
  set V := vecMulVec (A *ᵥ a) a with hV
  have h1 : vecMulVec (bvec A a) (bvec A a) = q⁻¹ • vecMulVec (A *ᵥ a) (A *ᵥ a) := by
    unfold bvec
    rw [smul_vecMulVec, vecMulVec_smul, smul_smul, ← hq, ← mul_inv,
      Real.mul_self_sqrt hqpos.le]
  have h2 : vecMulVec (A *ᵥ a) (A *ᵥ a) * A⁻¹ = V := by
    rw [vecMulVec_mul, vecMul_mulVec, hAT, hAinv, vecMul_one]
  have h3 : vecMulVec (A *ᵥ a) (A *ᵥ a) * vecMulVec a a = q • V := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, dotProduct_comm]
  have h5 : A * vecMulVec a a = V := by rw [mul_vecMulVec]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  set P := (2 * (n : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2 + 3)) •
        (A⁻¹ + ((2 / ((n : ℝ) - 1)) * q⁻¹) • vecMulVec a a) with hP
  have hprod : Astar A a * P = 1 := by
    unfold Astar
    rw [h1, hP]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, h2, h3, h5, hAinv, smul_add, smul_sub, smul_smul]
    have hn1' : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (n : ℝ) + 1 ≠ 0 := by linarith
    have hden : 2 * (n : ℝ) ^ 2 + 3 ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
  have hinv : (Astar A a)⁻¹ = P := Matrix.inv_eq_right_inv hprod
  have hPpos : P.PosDef := by
    rw [hP]
    apply PosDef.smul _ (by positivity)
    apply PosDef.add_posSemidef hA.inv
    apply PosSemidef.smul _ (by positivity)
    have := posSemidef_vecMulVec_self_star a
    simpa using this
  refine ⟨?_, hinv⟩
  rw [← posDef_inv_iff, hinv]
  exact hPpos
