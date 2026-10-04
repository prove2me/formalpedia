-- Prove2me | solution 1 for ErdosStraus242.family_mod643
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:03.086121+00:00
-- url     : https://prove2.me/submissions/0a6cb0c6-e959-438f-9155-218f11d9409c

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 643 ∈ ({639, 615, 551} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 643
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 643 * k + n % 643 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 639: alpha = 161, g = 1, beta = 160
    have hnform : n = 643 * k + 639 := by omega
    rw [hnform]
    refine ⟨161 * k + 160, 161 * (643 * k + 639), 161 * (161 * k + 160) * (643 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 161 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 643 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 615: alpha = 161, g = 7, beta = 154
    have hnform : n = 643 * k + 615 := by omega
    rw [hnform]
    refine ⟨161 * k + 154, 161 * (643 * k + 615), 23 * (161 * k + 154) * (643 * k + 615), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 161 * k + 154 := by nlinarith
      have hk2 : (0 : ℚ) < 643 * k + 615 := by nlinarith
      field_simp
      ring
  · -- class 551: alpha = 161, g = 23, beta = 138
    have hnform : n = 643 * k + 551 := by omega
    rw [hnform]
    refine ⟨161 * k + 138, 161 * (643 * k + 551), 7 * (161 * k + 138) * (643 * k + 551), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 161 * k + 138 := by nlinarith
      have hk2 : (0 : ℚ) < 643 * k + 551 := by nlinarith
      field_simp
      ring
