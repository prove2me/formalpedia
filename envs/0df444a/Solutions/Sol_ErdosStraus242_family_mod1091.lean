-- Prove2me | solution 1 for ErdosStraus242.family_mod1091
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:39.418613+00:00
-- url     : https://prove2.me/submissions/127fe875-2061-4fc6-b0a7-63535c6fcbbc

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1091 ∈ ({1087, 1079, 1063, 1039, 1007, 935, 727} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1091
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1091 * k + n % 1091 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 1087: alpha = 273, g = 1, beta = 272
    have hnform : n = 1091 * k + 1087 := by omega
    rw [hnform]
    refine ⟨273 * k + 272, 273 * (1091 * k + 1087), 273 * (273 * k + 272) * (1091 * k + 1087), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 273 * k + 272 := by nlinarith
      have hk2 : (0 : ℚ) < 1091 * k + 1087 := by nlinarith
      field_simp
      ring
  · -- class 1079: alpha = 273, g = 3, beta = 270
    have hnform : n = 1091 * k + 1079 := by omega
    rw [hnform]
    refine ⟨273 * k + 270, 273 * (1091 * k + 1079), 91 * (273 * k + 270) * (1091 * k + 1079), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 273 * k + 270 := by nlinarith
      have hk2 : (0 : ℚ) < 1091 * k + 1079 := by nlinarith
      field_simp
      ring
  · -- class 1063: alpha = 273, g = 7, beta = 266
    have hnform : n = 1091 * k + 1063 := by omega
    rw [hnform]
    refine ⟨273 * k + 266, 273 * (1091 * k + 1063), 39 * (273 * k + 266) * (1091 * k + 1063), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 273 * k + 266 := by nlinarith
      have hk2 : (0 : ℚ) < 1091 * k + 1063 := by nlinarith
      field_simp
      ring
  · -- class 1039: alpha = 273, g = 13, beta = 260
    have hnform : n = 1091 * k + 1039 := by omega
    rw [hnform]
    refine ⟨273 * k + 260, 273 * (1091 * k + 1039), 21 * (273 * k + 260) * (1091 * k + 1039), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 273 * k + 260 := by nlinarith
      have hk2 : (0 : ℚ) < 1091 * k + 1039 := by nlinarith
      field_simp
      ring
  · -- class 1007: alpha = 273, g = 21, beta = 252
    have hnform : n = 1091 * k + 1007 := by omega
    rw [hnform]
    refine ⟨273 * k + 252, 273 * (1091 * k + 1007), 13 * (273 * k + 252) * (1091 * k + 1007), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 273 * k + 252 := by nlinarith
      have hk2 : (0 : ℚ) < 1091 * k + 1007 := by nlinarith
      field_simp
      ring
  · -- class 935: alpha = 273, g = 39, beta = 234
    have hnform : n = 1091 * k + 935 := by omega
    rw [hnform]
    refine ⟨273 * k + 234, 273 * (1091 * k + 935), 7 * (273 * k + 234) * (1091 * k + 935), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 273 * k + 234 := by nlinarith
      have hk2 : (0 : ℚ) < 1091 * k + 935 := by nlinarith
      field_simp
      ring
  · -- class 727: alpha = 273, g = 91, beta = 182
    have hnform : n = 1091 * k + 727 := by omega
    rw [hnform]
    refine ⟨273 * k + 182, 273 * (1091 * k + 727), 3 * (273 * k + 182) * (1091 * k + 727), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 273 * k + 182 := by nlinarith
      have hk2 : (0 : ℚ) < 1091 * k + 727 := by nlinarith
      field_simp
      ring
