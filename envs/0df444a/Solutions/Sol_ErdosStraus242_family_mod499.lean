-- Prove2me | solution 1 for ErdosStraus242.family_mod499
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:35.119143+00:00
-- url     : https://prove2.me/submissions/792aaf2a-79e2-4f80-9e75-acdf369b385a

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 499 ∈ ({495, 479, 399} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 499
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 499 * k + n % 499 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 495: alpha = 125, g = 1, beta = 124
    have hnform : n = 499 * k + 495 := by omega
    rw [hnform]
    refine ⟨125 * k + 124, 125 * (499 * k + 495), 125 * (125 * k + 124) * (499 * k + 495), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 125 * k + 124 := by nlinarith
      have hk2 : (0 : ℚ) < 499 * k + 495 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 125, g = 5, beta = 120
    have hnform : n = 499 * k + 479 := by omega
    rw [hnform]
    refine ⟨125 * k + 120, 125 * (499 * k + 479), 25 * (125 * k + 120) * (499 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 125 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 499 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 399: alpha = 125, g = 25, beta = 100
    have hnform : n = 499 * k + 399 := by omega
    rw [hnform]
    refine ⟨125 * k + 100, 125 * (499 * k + 399), 5 * (125 * k + 100) * (499 * k + 399), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 125 * k + 100 := by nlinarith
      have hk2 : (0 : ℚ) < 499 * k + 399 := by nlinarith
      field_simp
      ring
