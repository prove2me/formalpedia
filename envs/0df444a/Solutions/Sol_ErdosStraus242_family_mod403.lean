-- Prove2me | solution 1 for ErdosStraus242.family_mod403
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:32.660465+00:00
-- url     : https://prove2.me/submissions/0e981e96-50bd-44b1-a60b-060452feae92

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 403 ∈ ({399} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 403
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 403 * k + n % 403 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 399: alpha = 101, g = 1, beta = 100
    have hnform : n = 403 * k + 399 := by omega
    rw [hnform]
    refine ⟨101 * k + 100, 101 * (403 * k + 399), 101 * (101 * k + 100) * (403 * k + 399), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 101 * k + 100 := by nlinarith
      have hk2 : (0 : ℚ) < 403 * k + 399 := by nlinarith
      field_simp
      ring
