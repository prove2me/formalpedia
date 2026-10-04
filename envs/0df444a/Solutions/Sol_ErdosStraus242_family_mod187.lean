-- Prove2me | solution 1 for ErdosStraus242.family_mod187
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:31.167631+00:00
-- url     : https://prove2.me/submissions/4b9e0d47-f7e4-44cf-9d98-2f00024590bc

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 187 ∈ ({183} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 187
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 187 * k + n % 187 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 183: alpha = 47, g = 1, beta = 46
    have hnform : n = 187 * k + 183 := by omega
    rw [hnform]
    refine ⟨47 * k + 46, 47 * (187 * k + 183), 47 * (47 * k + 46) * (187 * k + 183), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 47 * k + 46 := by nlinarith
      have hk2 : (0 : ℚ) < 187 * k + 183 := by nlinarith
      field_simp
      ring
