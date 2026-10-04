-- Prove2me | solution 2 for ErdosStraus242.family_mod691
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:23.085332+00:00
-- url     : https://prove2.me/submissions/988fb07d-4dfb-4160-b3b7-41ff9f1acf41

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 691 ∈ ({687} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 691
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 691 * k + n % 691 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 687: alpha = 173, g = 1, beta = 172
    have hnform : n = 691 * k + 687 := by omega
    rw [hnform]
    refine ⟨173 * k + 172, 173 * (691 * k + 687), 173 * (173 * k + 172) * (691 * k + 687), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 173 * k + 172 := by nlinarith
      have hk2 : (0 : ℚ) < 691 * k + 687 := by nlinarith
      field_simp
      ring
