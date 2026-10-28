-- Prove2me | solution 1 for BitDFT.scalar_magnitude_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:59:24.001547+00:00
-- url     : https://prove2.me/submissions/5c18b62f-181a-496f-8d88-df858205a77e

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
open BitDFT IntMul

private theorem bin_head (q a : ℕ) : bin (q+1) a = a.testBit q :: bin q a := by
  unfold bin
  rw [List.ofFn_succ]
  congr 1
  congr 1
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

private theorem bin_boundary (q : ℕ) : bin q (2^q) = List.replicate q false := by
  unfold bin
  rw [← List.ofFn_const]
  congr 1
  funext i
  apply Nat.testBit_two_pow_of_ne
  have := i.isLt
  omega

/-- The leading magnitude bit chooses between a q-bit multiplier call and a shift.
    This result has no smoothness assumption on any runtime bound. -/
theorem solution (q a n : ℕ) (ha : a ≤ 2^q) :
    (a < 2^q ∧ bin (q+1) a = false :: bin q a) ∨
    (a = 2^q ∧ bin (q+1) a = true :: List.replicate q false ∧
      n*a = n*2^q) := by
  rcases lt_or_eq_of_le ha with hlt | heq
  · left
    exact ⟨hlt, by rw [bin_head,Nat.testBit_eq_false_of_lt hlt]⟩
  · right
    subst a
    refine ⟨rfl,?_,rfl⟩
    rw [bin_head,bin_boundary]
    simp
