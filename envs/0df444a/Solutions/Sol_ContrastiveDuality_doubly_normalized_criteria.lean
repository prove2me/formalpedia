-- Prove2me | solution 1 for ContrastiveDuality.doubly_normalized_criteria
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:56:04.150351+00:00
-- url     : https://prove2.me/submissions/c8f88ed0-f4b6-45d2-be25-fd47272a9fab

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
namespace ContrastiveDuality

lemma cd_frob_tr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = Matrix.trace (A * Aᵀ) := by
  unfold frobSq
  simp [Matrix.trace, Matrix.mul_apply, sq]

lemma cd_frob_sym {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    frobSq (Kᵀ * K) = frobSq (K * Kᵀ) := by
  rw [cd_frob_tr, cd_frob_tr, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

lemma cd_frob_sub_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobSq (A - extractedDiag A) = frobSq A - ∑ i, A i i ^ 2 := by
  unfold frobSq extractedDiag
  have e : ∀ i j, ((A - Matrix.diagonal fun i => A i i) i j) ^ 2 =
      A i j ^ 2 - (if i = j then A i i ^ 2 else 0) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; ring
    · ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma cd_col_sq {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (i : Fin N) :
    (Kᵀ * K) i i = colNorm K i ^ 2 := by
  unfold colNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  simp [Matrix.mul_apply, sq]

lemma cd_row_sq {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (j : Fin M) :
    (K * Kᵀ) j j = rowNorm K j ^ 2 := by
  unfold rowNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  simp [Matrix.mul_apply, sq]

lemma cd_trace_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (A * extractedDiag A) = ∑ i, A i i ^ 2 := by
  unfold extractedDiag
  simp [Matrix.trace, Matrix.mul_diagonal, sq]

theorem doubly_normalized_criteria {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ)
    (hcol : ∀ i, colNorm K i = 1) (hrow : ∀ j, rowNorm K j = 1) :
    nonContrastiveCriterion K = contrastiveCriterion K + (N : ℝ) - (M : ℝ) := by
  unfold nonContrastiveCriterion contrastiveCriterion
  rw [cd_frob_sub_diag, cd_frob_sub_diag, cd_frob_sym K]
  have h1 : ∑ i, (Kᵀ * K) i i ^ 2 = N := by
    simp [cd_col_sq, hcol]
  have h2 : ∑ j, (K * Kᵀ) j j ^ 2 = M := by
    simp [cd_row_sq, hrow]
  rw [h1, h2]; ring

end ContrastiveDuality

open ContrastiveDuality in
theorem solution {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ)
    (hcol : ∀ i, colNorm K i = 1) (hrow : ∀ j, rowNorm K j = 1) :
    nonContrastiveCriterion K = contrastiveCriterion K + (N : ℝ) - (M : ℝ) :=
  ContrastiveDuality.doubly_normalized_criteria K hcol hrow
