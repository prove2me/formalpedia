-- Prove2me | solution 1 for ErdosStraus242.family_mod1051
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:36.924894+00:00
-- url     : https://prove2.me/submissions/335ed3a9-4c83-4bad-91a2-2df0417a56f1

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1051 ∈ ({1047} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1051
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1051 * k + n % 1051 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 1047: alpha = 263, g = 1, beta = 262
    have hnform : n = 1051 * k + 1047 := by omega
    rw [hnform]
    refine ⟨263 * k + 262, 263 * (1051 * k + 1047), 263 * (263 * k + 262) * (1051 * k + 1047), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 263 * k + 262 := by nlinarith
      have hk2 : (0 : ℚ) < 1051 * k + 1047 := by nlinarith
      field_simp
      ring
