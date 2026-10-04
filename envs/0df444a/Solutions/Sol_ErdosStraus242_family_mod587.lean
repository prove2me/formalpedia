-- Prove2me | solution 1 for ErdosStraus242.family_mod587
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:40.255681+00:00
-- url     : https://prove2.me/submissions/80c03a02-751b-486a-97bb-6c9b0962a749

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 587 ∈ ({583, 575, 559, 503, 391} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 587
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 587 * k + n % 587 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 583: alpha = 147, g = 1, beta = 146
    have hnform : n = 587 * k + 583 := by omega
    rw [hnform]
    refine ⟨147 * k + 146, 147 * (587 * k + 583), 147 * (147 * k + 146) * (587 * k + 583), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 147 * k + 146 := by nlinarith
      have hk2 : (0 : ℚ) < 587 * k + 583 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 147, g = 3, beta = 144
    have hnform : n = 587 * k + 575 := by omega
    rw [hnform]
    refine ⟨147 * k + 144, 147 * (587 * k + 575), 49 * (147 * k + 144) * (587 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 147 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 587 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 559: alpha = 147, g = 7, beta = 140
    have hnform : n = 587 * k + 559 := by omega
    rw [hnform]
    refine ⟨147 * k + 140, 147 * (587 * k + 559), 21 * (147 * k + 140) * (587 * k + 559), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 147 * k + 140 := by nlinarith
      have hk2 : (0 : ℚ) < 587 * k + 559 := by nlinarith
      field_simp
      ring
  · -- class 503: alpha = 147, g = 21, beta = 126
    have hnform : n = 587 * k + 503 := by omega
    rw [hnform]
    refine ⟨147 * k + 126, 147 * (587 * k + 503), 7 * (147 * k + 126) * (587 * k + 503), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 147 * k + 126 := by nlinarith
      have hk2 : (0 : ℚ) < 587 * k + 503 := by nlinarith
      field_simp
      ring
  · -- class 391: alpha = 147, g = 49, beta = 98
    have hnform : n = 587 * k + 391 := by omega
    rw [hnform]
    refine ⟨147 * k + 98, 147 * (587 * k + 391), 3 * (147 * k + 98) * (587 * k + 391), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 147 * k + 98 := by nlinarith
      have hk2 : (0 : ℚ) < 587 * k + 391 := by nlinarith
      field_simp
      ring
