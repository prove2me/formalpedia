-- Prove2me | solution 1 for ErdosStraus242.family_mod67
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:39:39.190694+00:00
-- url     : https://prove2.me/submissions/a23b81f7-28bc-4025-874d-e4229ac80c74

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 67 ∈ ({63} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 67
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 67 * k + n % 67 := by dsimp [k]; omega
  simp only [Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 63: alpha = 17, g = 1, beta = 16
    have hnform : n = 67 * k + 63 := by omega
    rw [hnform]
    refine ⟨17 * k + 16, 17 * (67 * k + 63), 17 * (17 * k + 16) * (67 * k + 63), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 17 * k + 16 := by nlinarith
      have hk2 : (0 : ℚ) < 67 * k + 63 := by nlinarith
      field_simp
      ring
