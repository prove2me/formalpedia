-- Prove2me | solution 1 for ErdosStraus242.family_mod1171
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:44.228266+00:00
-- url     : https://prove2.me/submissions/508c9c90-0142-4ff4-8b21-1e6c20ae46fc

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1171 ∈ ({1167} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1171
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1171 * k + n % 1171 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 1167: alpha = 293, g = 1, beta = 292
    have hnform : n = 1171 * k + 1167 := by omega
    rw [hnform]
    refine ⟨293 * k + 292, 293 * (1171 * k + 1167), 293 * (293 * k + 292) * (1171 * k + 1167), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 293 * k + 292 := by nlinarith
      have hk2 : (0 : ℚ) < 1171 * k + 1167 := by nlinarith
      field_simp
      ring
