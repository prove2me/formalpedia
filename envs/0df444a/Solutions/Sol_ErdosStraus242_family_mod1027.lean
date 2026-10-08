-- Prove2me | solution 1 for ErdosStraus242.family_mod1027
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:35.487012+00:00
-- url     : https://prove2.me/submissions/fbc0bce7-9b51-4b67-beb3-1db9f665f342

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1027 ∈ ({1023} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1027
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1027 * k + n % 1027 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 1023: alpha = 257, g = 1, beta = 256
    have hnform : n = 1027 * k + 1023 := by omega
    rw [hnform]
    refine ⟨257 * k + 256, 257 * (1027 * k + 1023), 257 * (257 * k + 256) * (1027 * k + 1023), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 257 * k + 256 := by nlinarith
      have hk2 : (0 : ℚ) < 1027 * k + 1023 := by nlinarith
      field_simp
      ring
