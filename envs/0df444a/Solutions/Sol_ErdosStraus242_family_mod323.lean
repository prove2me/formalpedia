-- Prove2me | solution 1 for ErdosStraus242.family_mod323
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:44:42.207776+00:00
-- url     : https://prove2.me/submissions/1045bb82-9df3-4eb9-8b0d-5a182156825e

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 323 ∈ ({319, 311, 287, 215} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 323
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 323 * k + n % 323 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h
  · -- class 319: alpha = 81, g = 1, beta = 80
    have hnform : n = 323 * k + 319 := by omega
    rw [hnform]
    refine ⟨81 * k + 80, 81 * (323 * k + 319), 81 * (81 * k + 80) * (323 * k + 319), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 81 * k + 80 := by nlinarith
      have hk2 : (0 : ℚ) < 323 * k + 319 := by nlinarith
      field_simp
      ring
  · -- class 311: alpha = 81, g = 3, beta = 78
    have hnform : n = 323 * k + 311 := by omega
    rw [hnform]
    refine ⟨81 * k + 78, 81 * (323 * k + 311), 27 * (81 * k + 78) * (323 * k + 311), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 81 * k + 78 := by nlinarith
      have hk2 : (0 : ℚ) < 323 * k + 311 := by nlinarith
      field_simp
      ring
  · -- class 287: alpha = 81, g = 9, beta = 72
    have hnform : n = 323 * k + 287 := by omega
    rw [hnform]
    refine ⟨81 * k + 72, 81 * (323 * k + 287), 9 * (81 * k + 72) * (323 * k + 287), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 81 * k + 72 := by nlinarith
      have hk2 : (0 : ℚ) < 323 * k + 287 := by nlinarith
      field_simp
      ring
  · -- class 215: alpha = 81, g = 27, beta = 54
    have hnform : n = 323 * k + 215 := by omega
    rw [hnform]
    refine ⟨81 * k + 54, 81 * (323 * k + 215), 3 * (81 * k + 54) * (323 * k + 215), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 81 * k + 54 := by nlinarith
      have hk2 : (0 : ℚ) < 323 * k + 215 := by nlinarith
      field_simp
      ring
