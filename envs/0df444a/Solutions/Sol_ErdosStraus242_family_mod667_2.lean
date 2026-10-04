-- Prove2me | solution 2 for ErdosStraus242.family_mod667
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:21.65208+00:00
-- url     : https://prove2.me/submissions/d6a46c97-b3de-4240-8ae3-4b592492f3de

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 667 ∈ ({663} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 667
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 667 * k + n % 667 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 663: alpha = 167, g = 1, beta = 166
    have hnform : n = 667 * k + 663 := by omega
    rw [hnform]
    refine ⟨167 * k + 166, 167 * (667 * k + 663), 167 * (167 * k + 166) * (667 * k + 663), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 167 * k + 166 := by nlinarith
      have hk2 : (0 : ℚ) < 667 * k + 663 := by nlinarith
      field_simp
      ring
