-- Prove2me | solution 1 for ErdosStraus242.family_mod1139
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:41.328912+00:00
-- url     : https://prove2.me/submissions/490c6b78-7b9c-423c-980e-95f8529ffff3

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1139 ∈ ({1135, 1127, 1119, 1079, 1063, 911, 759} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1139
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1139 * k + n % 1139 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 1135: alpha = 285, g = 1, beta = 284
    have hnform : n = 1139 * k + 1135 := by omega
    rw [hnform]
    refine ⟨285 * k + 284, 285 * (1139 * k + 1135), 285 * (285 * k + 284) * (1139 * k + 1135), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 285 * k + 284 := by nlinarith
      have hk2 : (0 : ℚ) < 1139 * k + 1135 := by nlinarith
      field_simp
      ring
  · -- class 1127: alpha = 285, g = 3, beta = 282
    have hnform : n = 1139 * k + 1127 := by omega
    rw [hnform]
    refine ⟨285 * k + 282, 285 * (1139 * k + 1127), 95 * (285 * k + 282) * (1139 * k + 1127), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 285 * k + 282 := by nlinarith
      have hk2 : (0 : ℚ) < 1139 * k + 1127 := by nlinarith
      field_simp
      ring
  · -- class 1119: alpha = 285, g = 5, beta = 280
    have hnform : n = 1139 * k + 1119 := by omega
    rw [hnform]
    refine ⟨285 * k + 280, 285 * (1139 * k + 1119), 57 * (285 * k + 280) * (1139 * k + 1119), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 285 * k + 280 := by nlinarith
      have hk2 : (0 : ℚ) < 1139 * k + 1119 := by nlinarith
      field_simp
      ring
  · -- class 1079: alpha = 285, g = 15, beta = 270
    have hnform : n = 1139 * k + 1079 := by omega
    rw [hnform]
    refine ⟨285 * k + 270, 285 * (1139 * k + 1079), 19 * (285 * k + 270) * (1139 * k + 1079), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 285 * k + 270 := by nlinarith
      have hk2 : (0 : ℚ) < 1139 * k + 1079 := by nlinarith
      field_simp
      ring
  · -- class 1063: alpha = 285, g = 19, beta = 266
    have hnform : n = 1139 * k + 1063 := by omega
    rw [hnform]
    refine ⟨285 * k + 266, 285 * (1139 * k + 1063), 15 * (285 * k + 266) * (1139 * k + 1063), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 285 * k + 266 := by nlinarith
      have hk2 : (0 : ℚ) < 1139 * k + 1063 := by nlinarith
      field_simp
      ring
  · -- class 911: alpha = 285, g = 57, beta = 228
    have hnform : n = 1139 * k + 911 := by omega
    rw [hnform]
    refine ⟨285 * k + 228, 285 * (1139 * k + 911), 5 * (285 * k + 228) * (1139 * k + 911), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 285 * k + 228 := by nlinarith
      have hk2 : (0 : ℚ) < 1139 * k + 911 := by nlinarith
      field_simp
      ring
  · -- class 759: alpha = 285, g = 95, beta = 190
    have hnform : n = 1139 * k + 759 := by omega
    rw [hnform]
    refine ⟨285 * k + 190, 285 * (1139 * k + 759), 3 * (285 * k + 190) * (1139 * k + 759), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 285 * k + 190 := by nlinarith
      have hk2 : (0 : ℚ) < 1139 * k + 759 := by nlinarith
      field_simp
      ring
