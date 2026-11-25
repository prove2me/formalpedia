-- Prove2me | solution 1 for ContrastiveDuality.norm_pow_four_bounds
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:57:34.721872+00:00
-- url     : https://prove2.me/submissions/30dadf2a-0571-42d1-8dc8-653777b5faf3

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

lemma cd_row_sq' {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (j : Fin M) :
    rowNorm K j ^ 2 = ∑ i, K j i ^ 2 := by
  unfold rowNorm; rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]

lemma cd_col_sq' {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) (i : Fin N) :
    colNorm K i ^ 2 = ∑ j, K j i ^ 2 := by
  unfold colNorm; rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]

lemma cd_sum_eq {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    ∑ j, rowNorm K j ^ 2 = ∑ i, colNorm K i ^ 2 := by
  simp only [cd_row_sq', cd_col_sq']; exact Finset.sum_comm

lemma cd_sq_bounds {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, x i) ^ 2 / (Fintype.card ι : ℝ) ≤ ∑ i, x i ^ 2 ∧ ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  constructor
  · rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · rw [h]; simp only [Nat.cast_zero, div_zero]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    · rw [div_le_iff₀ (by exact_mod_cast h), mul_comm]
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
      simpa using this
  · have : ∀ i, x i ^ 2 ≤ x i * ∑ j, x j := fun i => by
      rw [sq]; exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)) (hx i)
    calc ∑ i, x i ^ 2 ≤ ∑ i, x i * ∑ j, x j := Finset.sum_le_sum (fun i _ => this i)
      _ = (∑ i, x i) ^ 2 := by rw [← Finset.sum_mul, sq]

lemma cd_pow4 {M N : ℕ} (hM : 0 < M) (K : Matrix (Fin M) (Fin N) ℝ) (a : ℝ)
    (h : ∀ i, colNorm K i = a) :
    (N : ℝ) ^ 2 / M * a ^ 4 ≤ ∑ j, rowNorm K j ^ 4 ∧ ∑ j, rowNorm K j ^ 4 ≤ (N : ℝ) ^ 2 * a ^ 4 := by
  have hs : ∑ j, rowNorm K j ^ 2 = N * a ^ 2 := by
    rw [cd_sum_eq]; simp [h]
  have hb := cd_sq_bounds (fun j => rowNorm K j ^ 2) (fun j => sq_nonneg _)
  simp only [Fintype.card_fin, hs] at hb
  have e : ∀ j, (rowNorm K j ^ 2) ^ 2 = rowNorm K j ^ 4 := fun j => by ring
  simp only [e] at hb
  constructor
  · have : (N * a ^ 2) ^ 2 / (M : ℝ) = (N : ℝ) ^ 2 / M * a ^ 4 := by ring
    linarith [hb.1]
  · have : (N * a ^ 2 : ℝ) ^ 2 = (N : ℝ) ^ 2 * a ^ 4 := by ring
    linarith [hb.2]

lemma cd_pow4' {M N : ℕ} (hN : 0 < N) (K : Matrix (Fin M) (Fin N) ℝ) (a : ℝ)
    (h : ∀ j, rowNorm K j = a) :
    (M : ℝ) ^ 2 / N * a ^ 4 ≤ ∑ i, colNorm K i ^ 4 ∧ ∑ i, colNorm K i ^ 4 ≤ (M : ℝ) ^ 2 * a ^ 4 := by
  have hs : ∑ i, colNorm K i ^ 2 = M * a ^ 2 := by
    rw [← cd_sum_eq]; simp [h]
  have hb := cd_sq_bounds (fun i => colNorm K i ^ 2) (fun i => sq_nonneg _)
  simp only [Fintype.card_fin, hs] at hb
  have e : ∀ i, (colNorm K i ^ 2) ^ 2 = colNorm K i ^ 4 := fun i => by ring
  simp only [e] at hb
  constructor
  · have : (M * a ^ 2) ^ 2 / (N : ℝ) = (M : ℝ) ^ 2 / N * a ^ 4 := by ring
    linarith [hb.1]
  · have : (M * a ^ 2 : ℝ) ^ 2 = (M : ℝ) ^ 2 * a ^ 4 := by ring
    linarith [hb.2]

theorem norm_pow_four_bounds {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (K : Matrix (Fin M) (Fin N) ℝ) (a : ℝ) :
    ((∀ i, colNorm K i = a) →
      (N : ℝ) ^ 2 / M * a ^ 4 ≤ ∑ j, rowNorm K j ^ 4 ∧
        ∑ j, rowNorm K j ^ 4 ≤ (N : ℝ) ^ 2 * a ^ 4) ∧
    ((∀ j, rowNorm K j = a) →
      (M : ℝ) ^ 2 / N * a ^ 4 ≤ ∑ i, colNorm K i ^ 4 ∧
        ∑ i, colNorm K i ^ 4 ≤ (M : ℝ) ^ 2 * a ^ 4) := by
  exact ⟨fun h => cd_pow4 hM K a h, fun h => cd_pow4' hN K a h⟩

end ContrastiveDuality

open ContrastiveDuality in
theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (K : Matrix (Fin M) (Fin N) ℝ) (a : ℝ) :
    ((∀ i, colNorm K i = a) →
      (N : ℝ) ^ 2 / M * a ^ 4 ≤ ∑ j, rowNorm K j ^ 4 ∧
        ∑ j, rowNorm K j ^ 4 ≤ (N : ℝ) ^ 2 * a ^ 4) ∧
    ((∀ j, rowNorm K j = a) →
      (M : ℝ) ^ 2 / N * a ^ 4 ≤ ∑ i, colNorm K i ^ 4 ∧
        ∑ i, colNorm K i ^ 4 ≤ (M : ℝ) ^ 2 * a ^ 4) :=
  ContrastiveDuality.norm_pow_four_bounds hM hN K a
