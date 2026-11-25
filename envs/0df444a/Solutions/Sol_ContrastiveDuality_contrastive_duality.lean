-- Prove2me | solution 1 for ContrastiveDuality.contrastive_duality
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T01:42:40.026329+00:00
-- url     : https://prove2.me/submissions/4702151a-aca1-42c9-b2d7-91eb1614f2c2

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

/-- The squared Frobenius norm as a trace: `‖A‖_F² = tr (A * Aᵀ)`. -/
lemma frobSq_eq_trace_mul_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = Matrix.trace (A * Aᵀ) := by
  simp [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- Deleting the extracted diagonal subtracts the squares of the diagonal entries from the
squared Frobenius norm. -/
lemma frobSq_sub_extractedDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobSq (A - extractedDiag A) = frobSq A - ∑ i, A i i ^ 2 := by
  have key : ∀ i : Fin n,
      ∑ j, (A i j - extractedDiag A i j) ^ 2 = ∑ j, A i j ^ 2 - A i i ^ 2 := by
    intro i
    have hmem : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (A i j - extractedDiag A i j) ^ 2 = A i j ^ 2 := by
      intro j hj
      rw [Finset.mem_erase] at hj
      simp only [extractedDiag, Matrix.diagonal_apply, if_neg (Ne.symm hj.1), sub_zero]
    have hdiag : (A i i - extractedDiag A i i) ^ 2 = 0 := by
      simp only [extractedDiag, Matrix.diagonal_apply_eq, sub_self, pow_two, mul_zero]
    rw [← Finset.sum_erase_add _ (fun j => (A i j - extractedDiag A i j) ^ 2)
      (Finset.mem_univ i), hdiag, Finset.sum_congr rfl hmem]
    rw [← Finset.sum_erase_add _ (fun j => A i j ^ 2) (Finset.mem_univ i)]
    ring
  simp only [frobSq, Matrix.sub_apply]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib]

/-- The squared Frobenius norms of `K * Kᵀ` and `Kᵀ * K` agree. -/
lemma frobSq_mul_transpose {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    frobSq (K * Kᵀ) = frobSq (Kᵀ * K) := by
  rw [frobSq_eq_trace_mul_transpose (K * Kᵀ), frobSq_eq_trace_mul_transpose (Kᵀ * K)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (K : Matrix (Fin M) (Fin N) ℝ) (Kᵀ * (K * Kᵀ))]
  simp only [Matrix.mul_assoc]

/-- The fourth power of a column norm is the square of the sum of the squared entries of that
column. -/
lemma colNorm_pow_four {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (i : Fin N) :
    colNorm K i ^ 4 = (∑ j, K j i ^ 2) ^ 2 := by
  have h : 0 ≤ ∑ j, K j i ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [show colNorm K i ^ 4 = (colNorm K i ^ 2) ^ 2 by ring]
  rw [colNorm, Real.sq_sqrt h]

/-- The fourth power of a row norm is the square of the sum of the squared entries of that
row. -/
lemma rowNorm_pow_four {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (j : Fin M) :
    rowNorm K j ^ 4 = (∑ i, K j i ^ 2) ^ 2 := by
  have h : 0 ≤ ∑ i, K j i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [show rowNorm K j ^ 4 = (rowNorm K j ^ 2) ^ 2 by ring]
  rw [rowNorm, Real.sq_sqrt h]

end ContrastiveDuality

open ContrastiveDuality in
/-- **Theorem 3.3** (Garrido et al., ICLR 2023): the sample-contrastive and
dimension-contrastive criteria of an embedding matrix are equal up to the fourth powers of its
row and column norms. -/
theorem solution {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    nonContrastiveCriterion K + ∑ j, rowNorm K j ^ 4 =
      contrastiveCriterion K + ∑ i, colNorm K i ^ 4 := by
  have hrow : ∀ j : Fin M, (K * Kᵀ) j j = ∑ i, K j i ^ 2 := by
    intro j
    simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hcol : ∀ i : Fin N, (Kᵀ * K) i i = ∑ j, K j i ^ 2 := by
    intro i
    simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hnc := frobSq_sub_extractedDiag (K * Kᵀ)
  have hc := frobSq_sub_extractedDiag (Kᵀ * K)
  have h1 : (∑ j, rowNorm K j ^ 4) = ∑ j, ((K * Kᵀ) j j) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by rw [rowNorm_pow_four, hrow j])
  have h2 : (∑ i, colNorm K i ^ 4) = ∑ i, ((Kᵀ * K) i i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [colNorm_pow_four, hcol i])
  simp only [nonContrastiveCriterion, contrastiveCriterion]
  rw [hnc, hc, h1, h2, frobSq_mul_transpose K]
  ring
