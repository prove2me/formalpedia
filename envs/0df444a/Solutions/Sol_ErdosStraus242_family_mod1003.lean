-- Prove2me | solution 1 for ErdosStraus242.family_mod1003
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:33.848133+00:00
-- url     : https://prove2.me/submissions/99ae940d-2491-4921-8c65-29d5439bcf0e

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1003 ∈ ({999} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1003
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1003 * k + n % 1003 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 999: alpha = 251, g = 1, beta = 250
    have hnform : n = 1003 * k + 999 := by omega
    rw [hnform]
    refine ⟨251 * k + 250, 251 * (1003 * k + 999), 251 * (251 * k + 250) * (1003 * k + 999), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 251 * k + 250 := by nlinarith
      have hk2 : (0 : ℚ) < 1003 * k + 999 := by nlinarith
      field_simp
      ring
