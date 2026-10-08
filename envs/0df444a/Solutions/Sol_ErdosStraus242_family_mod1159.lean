-- Prove2me | solution 1 for ErdosStraus242.family_mod1159
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:43.215307+00:00
-- url     : https://prove2.me/submissions/6a060ce7-3c5f-4c38-b512-73e1034e7c6f

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1159 ∈ ({1155, 1151, 1139, 1119, 1043, 927, 579} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1159
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1159 * k + n % 1159 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 1155: alpha = 290, g = 1, beta = 289
    have hnform : n = 1159 * k + 1155 := by omega
    rw [hnform]
    refine ⟨290 * k + 289, 290 * (1159 * k + 1155), 290 * (290 * k + 289) * (1159 * k + 1155), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 290 * k + 289 := by nlinarith
      have hk2 : (0 : ℚ) < 1159 * k + 1155 := by nlinarith
      field_simp
      ring
  · -- class 1151: alpha = 290, g = 2, beta = 288
    have hnform : n = 1159 * k + 1151 := by omega
    rw [hnform]
    refine ⟨290 * k + 288, 290 * (1159 * k + 1151), 145 * (290 * k + 288) * (1159 * k + 1151), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 290 * k + 288 := by nlinarith
      have hk2 : (0 : ℚ) < 1159 * k + 1151 := by nlinarith
      field_simp
      ring
  · -- class 1139: alpha = 290, g = 5, beta = 285
    have hnform : n = 1159 * k + 1139 := by omega
    rw [hnform]
    refine ⟨290 * k + 285, 290 * (1159 * k + 1139), 58 * (290 * k + 285) * (1159 * k + 1139), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 290 * k + 285 := by nlinarith
      have hk2 : (0 : ℚ) < 1159 * k + 1139 := by nlinarith
      field_simp
      ring
  · -- class 1119: alpha = 290, g = 10, beta = 280
    have hnform : n = 1159 * k + 1119 := by omega
    rw [hnform]
    refine ⟨290 * k + 280, 290 * (1159 * k + 1119), 29 * (290 * k + 280) * (1159 * k + 1119), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 290 * k + 280 := by nlinarith
      have hk2 : (0 : ℚ) < 1159 * k + 1119 := by nlinarith
      field_simp
      ring
  · -- class 1043: alpha = 290, g = 29, beta = 261
    have hnform : n = 1159 * k + 1043 := by omega
    rw [hnform]
    refine ⟨290 * k + 261, 290 * (1159 * k + 1043), 10 * (290 * k + 261) * (1159 * k + 1043), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 290 * k + 261 := by nlinarith
      have hk2 : (0 : ℚ) < 1159 * k + 1043 := by nlinarith
      field_simp
      ring
  · -- class 927: alpha = 290, g = 58, beta = 232
    have hnform : n = 1159 * k + 927 := by omega
    rw [hnform]
    refine ⟨290 * k + 232, 290 * (1159 * k + 927), 5 * (290 * k + 232) * (1159 * k + 927), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 290 * k + 232 := by nlinarith
      have hk2 : (0 : ℚ) < 1159 * k + 927 := by nlinarith
      field_simp
      ring
  · -- class 579: alpha = 290, g = 145, beta = 145
    have hnform : n = 1159 * k + 579 := by omega
    by_cases hk0 : k = 0
    · have h579 : n = 579 := by omega
      rw [h579]
      refine ⟨145, 83956, 7048525980, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨290 * k + 145, 290 * (1159 * k + 579), 2 * (290 * k + 145) * (1159 * k + 579), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 290 * k + 145 := by nlinarith
        have hk2 : (0 : ℚ) < 1159 * k + 579 := by nlinarith
        field_simp
        ring
