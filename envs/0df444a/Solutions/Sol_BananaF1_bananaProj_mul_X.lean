-- Prove2me | solution 1 for BananaF1.bananaProj_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:11:41.207093+00:00
-- url     : https://prove2.me/submissions/479f27cc-c21b-4795-8956-f50e00f1b693

import Definitions.Def_bananaF1Classes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
open Polynomial
open BananaF1

theorem solution (n : ℕ) :
    X * bananaProjClass n = (1 + X : Polynomial ℤ) ^ n - 1 := by
  rw [bananaProjClass, Finset.mul_sum, add_comm (1 : Polynomial ℤ) X, add_pow,
    Finset.sum_range_succ']
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one,
    add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_natCast]
  ring

theorem W3b_BananaF1_tail_succ (n : ℕ) : bananaTail (n + 1) = X ^ n - bananaTail n := by
  unfold bananaTail
  rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, map_one, one_mul]
  have key : ∑ j ∈ Finset.range n, C ((-1 : ℤ) ^ (n - j)) * X ^ j
      = -∑ j ∈ Finset.range n, C ((-1 : ℤ) ^ (n - 1 - j)) * X ^ j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.mp hj
    rw [show n - j = (n - 1 - j) + 1 by omega, pow_succ]
    simp
  rw [key]
  ring

theorem W3b_BananaF1_tail_mul_all (n : ℕ) :
    (X + 1) * bananaTail n = X ^ n - C ((-1 : ℤ) ^ n) := by
  induction n with
  | zero => simp [bananaTail]
  | succ n ih =>
    rw [W3b_BananaF1_tail_succ, mul_sub, ih, pow_succ (-1 : ℤ) n, map_mul, map_neg, map_one]
    ring

theorem W3b_BananaF1_bananaTail_mul_succ (n : ℕ) (hn : 1 ≤ n) :
    (X + 1) * bananaTail n = X ^ n - C ((-1 : ℤ) ^ n) :=
  W3b_BananaF1_tail_mul_all n

theorem W3b_BananaF1_proj_coeff (n k : ℕ) :
    (bananaProjClass n).coeff k = if k < n then (n.choose (k + 1) : ℤ) else 0 := by
  simp [bananaProjClass, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]

theorem W3b_BananaF1_tail_coeff (n k : ℕ) :
    (bananaTail n).coeff k = if k < n then (-1 : ℤ) ^ (n - 1 - k) else 0 := by
  simp only [bananaTail, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  simp [Finset.sum_ite_eq]

theorem W3b_BananaF1_comp_coeff (n k : ℕ) :
    (bananaComplementClass n).coeff k =
      (if k < n then (-1 : ℤ) ^ (n - 1 - k) else 0) + (if k = n - 2 then (n : ℤ) else 0) := by
  rw [bananaComplementClass, Polynomial.coeff_add, W3b_BananaF1_tail_coeff,
    Polynomial.coeff_C_mul_X_pow]

theorem W3b_BananaF1_bananaHypersurfaceClass_coeff (n k : ℕ) (hn : 3 ≤ n) :
    (bananaHypersurfaceClass n).coeff k =
      (if k < n then (n.choose (k + 1) : ℤ) - (-1 : ℤ) ^ (n - 1 - k) else 0)
        - (if k = n - 2 then (n : ℤ) else 0) := by
  rw [bananaHypersurfaceClass, Polynomial.coeff_sub, W3b_BananaF1_proj_coeff,
    W3b_BananaF1_comp_coeff]
  split_ifs <;> ring

theorem W3b_BananaF1_bananaHypersurfaceClass_coeff_zero (n : ℕ) (hn : 3 ≤ n) :
    (bananaHypersurfaceClass n).coeff 0 = (n : ℤ) + (-1 : ℤ) ^ n := by
  rw [W3b_BananaF1_bananaHypersurfaceClass_coeff n 0 hn, if_pos (show 0 < n by omega),
    if_neg (show ¬ (0 = n - 2) by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [zero_add, Nat.choose_one_right, Nat.sub_zero, Nat.add_sub_cancel, pow_succ]
  push_cast
  ring

theorem W3b_BananaF1_bananaComplementClass_coeff_neg (n : ℕ) (hn : 4 ≤ n) :
    (bananaComplementClass n).coeff (n - 4) = -1 := by
  rw [W3b_BananaF1_comp_coeff, if_pos (show n - 4 < n by omega),
    if_neg (show ¬ (n - 4 = n - 2) by omega),
    show n - 1 - (n - 4) = 3 by omega]
  norm_num

theorem W3b_BananaF1_bananaHypersurfaceClass_coeff_nonneg (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    0 ≤ (bananaHypersurfaceClass n).coeff k := by
  rw [W3b_BananaF1_bananaHypersurfaceClass_coeff n k hn]
  split_ifs with h1 h2 h2
  · rw [show n - 1 - k = 1 by omega, show k + 1 = n - 1 by omega,
      Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
    norm_num
  · have hc : 0 < n.choose (k + 1) := Nat.choose_pos (by omega)
    rcases neg_one_pow_eq_or ℤ (n - 1 - k) with h | h <;> rw [h] <;> omega
  · omega
  · simp
