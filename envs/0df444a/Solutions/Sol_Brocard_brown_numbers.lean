-- Prove2me | solution 1 for Brocard.brown_numbers
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-01T00:15:31.819979+00:00
-- url     : https://prove2.me/submissions/936fe944-cdbb-476a-b93f-d5bcf50b7d47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution :
    Nat.factorial 4 + 1 = 5 ^ 2 ∧ Nat.factorial 5 + 1 = 11 ^ 2 ∧
      Nat.factorial 7 + 1 = 71 ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.factorial]
