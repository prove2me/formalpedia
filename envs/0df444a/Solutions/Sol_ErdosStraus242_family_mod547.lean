-- Prove2me | solution 1 for ErdosStraus242.family_mod547
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:36.976505+00:00
-- url     : https://prove2.me/submissions/ce7690fc-22d9-4826-b96a-0c0e615b8487

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 547 ∈ ({543} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 547
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 547 * k + n % 547 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 543: alpha = 137, g = 1, beta = 136
    have hnform : n = 547 * k + 543 := by omega
    rw [hnform]
    refine ⟨137 * k + 136, 137 * (547 * k + 543), 137 * (137 * k + 136) * (547 * k + 543), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 137 * k + 136 := by nlinarith
      have hk2 : (0 : ℚ) < 547 * k + 543 := by nlinarith
      field_simp
      ring
