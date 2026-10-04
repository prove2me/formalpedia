-- Prove2me | solution 1 for ErdosStraus242.family_mod451
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:33.093297+00:00
-- url     : https://prove2.me/submissions/d732c8c5-f2c4-4f3a-9b3c-e1ea88104c5f

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 451 ∈ ({447} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 451
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 451 * k + n % 451 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 447: alpha = 113, g = 1, beta = 112
    have hnform : n = 451 * k + 447 := by omega
    rw [hnform]
    refine ⟨113 * k + 112, 113 * (451 * k + 447), 113 * (113 * k + 112) * (451 * k + 447), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 113 * k + 112 := by nlinarith
      have hk2 : (0 : ℚ) < 451 * k + 447 := by nlinarith
      field_simp
      ring
