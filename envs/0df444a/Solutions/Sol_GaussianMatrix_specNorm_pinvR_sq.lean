-- Prove2me | solution 1 for GaussianMatrix.specNorm_pinvR_sq
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:48:16.818976+00:00
-- url     : https://prove2.me/submissions/bf1f7fb0-3cc1-4c62-a592-924679ec7ab1

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

open scoped Matrix.Norms.L2Operator in
theorem solution {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ) :
    specNorm (pinvR A) ^ 2 = specNorm (A * Aᵀ)⁻¹ := by
  unfold specNorm pinvR
  have hsym : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have key : (Aᵀ * (A * Aᵀ)⁻¹)ᴴ * (Aᵀ * (A * Aᵀ)⁻¹) = (A * Aᵀ)⁻¹ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, hsym]
    by_cases hM : IsUnit (A * Aᵀ).det
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hM]; simp
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, key]
