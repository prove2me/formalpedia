-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.pair_of_card_two_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:21:46.698806+00:00
-- url     : https://prove2.me/submissions/1a5ac4b5-f1fb-4f3e-8fbe-c1d7920b451b

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
attribute [local simp] F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
omit [Fintype B]
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (s : Finset B) (hs : s.card = 2) (x : B) (hx : x ∈ s) :
    ∃ a : B, x ≠ a ∧ s = {x, a} := by
  classical
  obtain ⟨u, v, huv, hs⟩ := Finset.card_eq_two.mp hs
  have h : x = u ∨ x = v := by simpa [hs] using hx
  rcases h with rfl | rfl
  · exact ⟨v, huv, hs⟩
  · exact ⟨u, huv.symm, by simpa [Finset.pair_comm] using hs⟩
end F6SmallBlockTokenCapacity.TokenRun
