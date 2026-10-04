-- Prove2me | solution 1 for ErdosStraus242.family_mod563
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:39.2523+00:00
-- url     : https://prove2.me/submissions/ec7946b6-4e9e-419a-8e17-661de6896a33

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 563 ∈ ({559, 551, 375} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 563
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 563 * k + n % 563 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 559: alpha = 141, g = 1, beta = 140
    have hnform : n = 563 * k + 559 := by omega
    rw [hnform]
    refine ⟨141 * k + 140, 141 * (563 * k + 559), 141 * (141 * k + 140) * (563 * k + 559), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 141 * k + 140 := by nlinarith
      have hk2 : (0 : ℚ) < 563 * k + 559 := by nlinarith
      field_simp
      ring
  · -- class 551: alpha = 141, g = 3, beta = 138
    have hnform : n = 563 * k + 551 := by omega
    rw [hnform]
    refine ⟨141 * k + 138, 141 * (563 * k + 551), 47 * (141 * k + 138) * (563 * k + 551), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 141 * k + 138 := by nlinarith
      have hk2 : (0 : ℚ) < 563 * k + 551 := by nlinarith
      field_simp
      ring
  · -- class 375: alpha = 141, g = 47, beta = 94
    have hnform : n = 563 * k + 375 := by omega
    rw [hnform]
    refine ⟨141 * k + 94, 141 * (563 * k + 375), 3 * (141 * k + 94) * (563 * k + 375), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 141 * k + 94 := by nlinarith
      have hk2 : (0 : ℚ) < 563 * k + 375 := by nlinarith
      field_simp
      ring
