-- Prove2me | solution 1 for ErdosStraus242.family_mod787
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:30.024888+00:00
-- url     : https://prove2.me/submissions/efa1a358-37e8-418f-a02a-b4976d3e3cd0

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 787 ∈ ({783} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 787
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 787 * k + n % 787 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 783: alpha = 197, g = 1, beta = 196
    have hnform : n = 787 * k + 783 := by omega
    rw [hnform]
    refine ⟨197 * k + 196, 197 * (787 * k + 783), 197 * (197 * k + 196) * (787 * k + 783), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 197 * k + 196 := by nlinarith
      have hk2 : (0 : ℚ) < 787 * k + 783 := by nlinarith
      field_simp
      ring
