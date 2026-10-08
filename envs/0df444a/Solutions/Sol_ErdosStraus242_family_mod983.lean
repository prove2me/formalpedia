-- Prove2me | solution 1 for ErdosStraus242.family_mod983
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:07.61795+00:00
-- url     : https://prove2.me/submissions/e2a2429b-5d8f-49ad-b7dd-e814a4404417

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 983 ∈ ({979, 975, 971, 959, 819, 655, 491} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 983
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 983 * k + n % 983 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 979: alpha = 246, g = 1, beta = 245
    have hnform : n = 983 * k + 979 := by omega
    rw [hnform]
    refine ⟨246 * k + 245, 246 * (983 * k + 979), 246 * (246 * k + 245) * (983 * k + 979), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 246 * k + 245 := by nlinarith
      have hk2 : (0 : ℚ) < 983 * k + 979 := by nlinarith
      field_simp
      ring
  · -- class 975: alpha = 246, g = 2, beta = 244
    have hnform : n = 983 * k + 975 := by omega
    rw [hnform]
    refine ⟨246 * k + 244, 246 * (983 * k + 975), 123 * (246 * k + 244) * (983 * k + 975), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 246 * k + 244 := by nlinarith
      have hk2 : (0 : ℚ) < 983 * k + 975 := by nlinarith
      field_simp
      ring
  · -- class 971: alpha = 246, g = 3, beta = 243
    have hnform : n = 983 * k + 971 := by omega
    rw [hnform]
    refine ⟨246 * k + 243, 246 * (983 * k + 971), 82 * (246 * k + 243) * (983 * k + 971), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 246 * k + 243 := by nlinarith
      have hk2 : (0 : ℚ) < 983 * k + 971 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 246, g = 6, beta = 240
    have hnform : n = 983 * k + 959 := by omega
    rw [hnform]
    refine ⟨246 * k + 240, 246 * (983 * k + 959), 41 * (246 * k + 240) * (983 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 246 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 983 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 819: alpha = 246, g = 41, beta = 205
    have hnform : n = 983 * k + 819 := by omega
    rw [hnform]
    refine ⟨246 * k + 205, 246 * (983 * k + 819), 6 * (246 * k + 205) * (983 * k + 819), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 246 * k + 205 := by nlinarith
      have hk2 : (0 : ℚ) < 983 * k + 819 := by nlinarith
      field_simp
      ring
  · -- class 655: alpha = 246, g = 82, beta = 164
    have hnform : n = 983 * k + 655 := by omega
    rw [hnform]
    refine ⟨246 * k + 164, 246 * (983 * k + 655), 3 * (246 * k + 164) * (983 * k + 655), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 246 * k + 164 := by nlinarith
      have hk2 : (0 : ℚ) < 983 * k + 655 := by nlinarith
      field_simp
      ring
  · -- class 491: alpha = 246, g = 123, beta = 123
    have hnform : n = 983 * k + 491 := by omega
    by_cases hk0 : k = 0
    · have h491 : n = 491 := by omega
      rw [h491]
      refine ⟨123, 60394, 3647374842, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨246 * k + 123, 246 * (983 * k + 491), 2 * (246 * k + 123) * (983 * k + 491), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 246 * k + 123 := by nlinarith
        have hk2 : (0 : ℚ) < 983 * k + 491 := by nlinarith
        field_simp
        ring
