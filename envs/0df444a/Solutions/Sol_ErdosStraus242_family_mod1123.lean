-- Prove2me | solution 1 for ErdosStraus242.family_mod1123
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:40.889468+00:00
-- url     : https://prove2.me/submissions/6e01abe5-71ec-4c49-a106-706451f92408

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1123 ∈ ({1119} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1123
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1123 * k + n % 1123 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 1119: alpha = 281, g = 1, beta = 280
    have hnform : n = 1123 * k + 1119 := by omega
    rw [hnform]
    refine ⟨281 * k + 280, 281 * (1123 * k + 1119), 281 * (281 * k + 280) * (1123 * k + 1119), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 281 * k + 280 := by nlinarith
      have hk2 : (0 : ℚ) < 1123 * k + 1119 := by nlinarith
      field_simp
      ring
