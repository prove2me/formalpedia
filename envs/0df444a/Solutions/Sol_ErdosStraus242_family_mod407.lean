-- Prove2me | solution 1 for ErdosStraus242.family_mod407
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:44:42.829496+00:00
-- url     : https://prove2.me/submissions/ef7cd942-0208-44c7-8d5b-40e3c5e66fa1

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 407 ∈ ({403, 399, 395, 383, 339, 271, 203} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 407
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 407 * k + n % 407 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 403: alpha = 102, g = 1, beta = 101
    have hnform : n = 407 * k + 403 := by omega
    rw [hnform]
    refine ⟨102 * k + 101, 102 * (407 * k + 403), 102 * (102 * k + 101) * (407 * k + 403), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 102 * k + 101 := by nlinarith
      have hk2 : (0 : ℚ) < 407 * k + 403 := by nlinarith
      field_simp
      ring
  · -- class 399: alpha = 102, g = 2, beta = 100
    have hnform : n = 407 * k + 399 := by omega
    rw [hnform]
    refine ⟨102 * k + 100, 102 * (407 * k + 399), 51 * (102 * k + 100) * (407 * k + 399), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 102 * k + 100 := by nlinarith
      have hk2 : (0 : ℚ) < 407 * k + 399 := by nlinarith
      field_simp
      ring
  · -- class 395: alpha = 102, g = 3, beta = 99
    have hnform : n = 407 * k + 395 := by omega
    rw [hnform]
    refine ⟨102 * k + 99, 102 * (407 * k + 395), 34 * (102 * k + 99) * (407 * k + 395), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 102 * k + 99 := by nlinarith
      have hk2 : (0 : ℚ) < 407 * k + 395 := by nlinarith
      field_simp
      ring
  · -- class 383: alpha = 102, g = 6, beta = 96
    have hnform : n = 407 * k + 383 := by omega
    rw [hnform]
    refine ⟨102 * k + 96, 102 * (407 * k + 383), 17 * (102 * k + 96) * (407 * k + 383), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 102 * k + 96 := by nlinarith
      have hk2 : (0 : ℚ) < 407 * k + 383 := by nlinarith
      field_simp
      ring
  · -- class 339: alpha = 102, g = 17, beta = 85
    have hnform : n = 407 * k + 339 := by omega
    rw [hnform]
    refine ⟨102 * k + 85, 102 * (407 * k + 339), 6 * (102 * k + 85) * (407 * k + 339), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 102 * k + 85 := by nlinarith
      have hk2 : (0 : ℚ) < 407 * k + 339 := by nlinarith
      field_simp
      ring
  · -- class 271: alpha = 102, g = 34, beta = 68
    have hnform : n = 407 * k + 271 := by omega
    rw [hnform]
    refine ⟨102 * k + 68, 102 * (407 * k + 271), 3 * (102 * k + 68) * (407 * k + 271), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 102 * k + 68 := by nlinarith
      have hk2 : (0 : ℚ) < 407 * k + 271 := by nlinarith
      field_simp
      ring
  · -- class 203: alpha = 102, g = 51, beta = 51
    have hnform : n = 407 * k + 203 := by omega
    by_cases hk0 : k = 0
    · have h203 : n = 203 := by omega
      rw [h203]
      refine ⟨51, 10354, 107194962, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨102 * k + 51, 102 * (407 * k + 203), 2 * (102 * k + 51) * (407 * k + 203), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 102 * k + 51 := by nlinarith
        have hk2 : (0 : ℚ) < 407 * k + 203 := by nlinarith
        field_simp
        ring
