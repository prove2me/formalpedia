-- Prove2me | solution 1 for ErdosStraus242.family_mod923
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:04.00154+00:00
-- url     : https://prove2.me/submissions/9877b112-dcbc-4c3c-aef4-6b65d501cba2

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 923 ∈ ({919, 911, 895, 879, 839, 791, 615} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 923
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 923 * k + n % 923 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 919: alpha = 231, g = 1, beta = 230
    have hnform : n = 923 * k + 919 := by omega
    rw [hnform]
    refine ⟨231 * k + 230, 231 * (923 * k + 919), 231 * (231 * k + 230) * (923 * k + 919), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 231 * k + 230 := by nlinarith
      have hk2 : (0 : ℚ) < 923 * k + 919 := by nlinarith
      field_simp
      ring
  · -- class 911: alpha = 231, g = 3, beta = 228
    have hnform : n = 923 * k + 911 := by omega
    rw [hnform]
    refine ⟨231 * k + 228, 231 * (923 * k + 911), 77 * (231 * k + 228) * (923 * k + 911), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 231 * k + 228 := by nlinarith
      have hk2 : (0 : ℚ) < 923 * k + 911 := by nlinarith
      field_simp
      ring
  · -- class 895: alpha = 231, g = 7, beta = 224
    have hnform : n = 923 * k + 895 := by omega
    rw [hnform]
    refine ⟨231 * k + 224, 231 * (923 * k + 895), 33 * (231 * k + 224) * (923 * k + 895), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 231 * k + 224 := by nlinarith
      have hk2 : (0 : ℚ) < 923 * k + 895 := by nlinarith
      field_simp
      ring
  · -- class 879: alpha = 231, g = 11, beta = 220
    have hnform : n = 923 * k + 879 := by omega
    rw [hnform]
    refine ⟨231 * k + 220, 231 * (923 * k + 879), 21 * (231 * k + 220) * (923 * k + 879), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 231 * k + 220 := by nlinarith
      have hk2 : (0 : ℚ) < 923 * k + 879 := by nlinarith
      field_simp
      ring
  · -- class 839: alpha = 231, g = 21, beta = 210
    have hnform : n = 923 * k + 839 := by omega
    rw [hnform]
    refine ⟨231 * k + 210, 231 * (923 * k + 839), 11 * (231 * k + 210) * (923 * k + 839), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 231 * k + 210 := by nlinarith
      have hk2 : (0 : ℚ) < 923 * k + 839 := by nlinarith
      field_simp
      ring
  · -- class 791: alpha = 231, g = 33, beta = 198
    have hnform : n = 923 * k + 791 := by omega
    rw [hnform]
    refine ⟨231 * k + 198, 231 * (923 * k + 791), 7 * (231 * k + 198) * (923 * k + 791), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 231 * k + 198 := by nlinarith
      have hk2 : (0 : ℚ) < 923 * k + 791 := by nlinarith
      field_simp
      ring
  · -- class 615: alpha = 231, g = 77, beta = 154
    have hnform : n = 923 * k + 615 := by omega
    rw [hnform]
    refine ⟨231 * k + 154, 231 * (923 * k + 615), 3 * (231 * k + 154) * (923 * k + 615), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 231 * k + 154 := by nlinarith
      have hk2 : (0 : ℚ) < 923 * k + 615 := by nlinarith
      field_simp
      ring
