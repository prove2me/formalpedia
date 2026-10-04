-- Prove2me | solution 1 for ErdosStraus242.family_mod523
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:36.06316+00:00
-- url     : https://prove2.me/submissions/dcf15175-fd02-4724-aa71-2c633aab6716

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 523 ∈ ({519} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 523
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 523 * k + n % 523 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 519: alpha = 131, g = 1, beta = 130
    have hnform : n = 523 * k + 519 := by omega
    rw [hnform]
    refine ⟨131 * k + 130, 131 * (523 * k + 519), 131 * (131 * k + 130) * (523 * k + 519), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 131 * k + 130 := by nlinarith
      have hk2 : (0 : ℚ) < 523 * k + 519 := by nlinarith
      field_simp
      ring
