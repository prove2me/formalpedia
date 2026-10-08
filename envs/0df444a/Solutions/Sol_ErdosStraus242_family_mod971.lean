-- Prove2me | solution 1 for ErdosStraus242.family_mod971
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:06.4891+00:00
-- url     : https://prove2.me/submissions/0e4503db-ebbb-4396-8eb0-a131136b67e6

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 971 ∈ ({967, 959, 935, 863, 647} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 971
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 971 * k + n % 971 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 967: alpha = 243, g = 1, beta = 242
    have hnform : n = 971 * k + 967 := by omega
    rw [hnform]
    refine ⟨243 * k + 242, 243 * (971 * k + 967), 243 * (243 * k + 242) * (971 * k + 967), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 243 * k + 242 := by nlinarith
      have hk2 : (0 : ℚ) < 971 * k + 967 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 243, g = 3, beta = 240
    have hnform : n = 971 * k + 959 := by omega
    rw [hnform]
    refine ⟨243 * k + 240, 243 * (971 * k + 959), 81 * (243 * k + 240) * (971 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 243 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 971 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 935: alpha = 243, g = 9, beta = 234
    have hnform : n = 971 * k + 935 := by omega
    rw [hnform]
    refine ⟨243 * k + 234, 243 * (971 * k + 935), 27 * (243 * k + 234) * (971 * k + 935), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 243 * k + 234 := by nlinarith
      have hk2 : (0 : ℚ) < 971 * k + 935 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 243, g = 27, beta = 216
    have hnform : n = 971 * k + 863 := by omega
    rw [hnform]
    refine ⟨243 * k + 216, 243 * (971 * k + 863), 9 * (243 * k + 216) * (971 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 243 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 971 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 647: alpha = 243, g = 81, beta = 162
    have hnform : n = 971 * k + 647 := by omega
    rw [hnform]
    refine ⟨243 * k + 162, 243 * (971 * k + 647), 3 * (243 * k + 162) * (971 * k + 647), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 243 * k + 162 := by nlinarith
      have hk2 : (0 : ℚ) < 971 * k + 647 := by nlinarith
      field_simp
      ring
