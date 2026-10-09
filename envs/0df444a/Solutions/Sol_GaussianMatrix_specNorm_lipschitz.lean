-- Prove2me | solution 1 for GaussianMatrix.specNorm_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:35:14.129494+00:00
-- url     : https://prove2.me/submissions/28ba6e43-d197-4ab8-a66b-690b51e4d8be

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Row-wise Cauchy–Schwarz: `‖B x‖₂² ≤ ‖B‖_F² ‖x‖₂²`. -/
lemma specNormLip_mulVec_dot_le {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ frobSq B * (x ⬝ᵥ x) := by
  unfold frobSq
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) x
  calc (∑ j, B i j * x j) * (∑ j, B i j * x j) = (∑ j, B i j * x j) ^ 2 := by ring
    _ ≤ (∑ j, B i j ^ 2) * ∑ j, x j ^ 2 := h
    _ = (∑ j, B i j ^ 2) * ∑ j, x j * x j := by simp only [sq]

lemma specNormLip_frobSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ) :
    0 ≤ frobSq B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma specNormLip_euclid_norm {n : Type*} [Fintype n] (v : EuclideanSpace ℝ n) :
    ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

/-- The `ℓ₂ → ℓ₂` operator norm is at most the Frobenius norm. -/
lemma specNorm_le_frobNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℝ) : specNorm B ≤ frobNorm B := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  show ‖(Matrix.toEuclideanLin B x)‖ ≤ frobNorm B * ‖x‖
  rw [specNormLip_euclid_norm, specNormLip_euclid_norm, frobNorm, ← Real.sqrt_mul
    (specNormLip_frobSq_nonneg B)]
  exact Real.sqrt_le_sqrt (specNormLip_mulVec_dot_le B x.ofLp)

open scoped Matrix.Norms.L2Operator in
lemma specNorm_sub_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℝ) : |specNorm A - specNorm B| ≤ specNorm (A - B) :=
  abs_norm_sub_norm_le A B

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (A B : Matrix (Fin N) (Fin n) ℝ) :
    |specNorm A - specNorm B| ≤ frobNorm (A - B) := by
  exact (specNorm_sub_le A B).trans (specNorm_le_frobNorm (A - B))
