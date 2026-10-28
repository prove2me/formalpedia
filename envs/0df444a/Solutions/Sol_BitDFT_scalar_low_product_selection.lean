-- Prove2me | solution 1 for BitDFT.scalar_low_product_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:07:41.117643+00:00
-- url     : https://prove2.me/submissions/387d1cd4-8238-4087-8be1-2a446d47852c

import Definitions.Def_BitDFT_Numerics
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
open BitDFT IntMul

/-- Every magnitude uses the same q-bit multiplication; its high bit only selects serialization. -/
theorem solution (q a n : ℕ) (ha : a ≤ 2^q) :
    a % 2^q < 2^q ∧
    n*a = (if a.testBit q then n*2^q else n*(a % 2^q)) ∧
    (a.testBit q = true → a % 2^q = 0 ∧ n*(a % 2^q) = 0) := by
  refine ⟨Nat.mod_lt _ (by positivity),?_,?_⟩
  · rcases lt_or_eq_of_le ha with h | h
    · rw [Nat.testBit_eq_false_of_lt h,Nat.mod_eq_of_lt h]
      rfl
    · subst a
      simp
  · intro hh
    have he : a = 2^q := by
      rcases lt_or_eq_of_le ha with h | h
      · rw [Nat.testBit_eq_false_of_lt h] at hh
        contradiction
      · exact h
    subst a
    simp
