-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.previous_holder_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:17:32.783027+00:00
-- url     : https://prove2.me/submissions/5c00768a-520d-4d81-9f44-17e233fbb1c9

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
omit [Fintype B] [Fintype W]
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (s : Finset B) (before after : B ≃ W)
    (hout : ∀ b, b ∉ s → before b = after b) {x : B} (hx : x ∈ s) :
    before.symm (after x) ∈ s := by
  classical
  by_contra hn
  have hfix := hout (before.symm (after x)) hn
  have heq : after (before.symm (after x)) = after x := by
    rw [← hfix, before.apply_symm_apply]
  have hsame := after.injective heq
  exact hn (hsame.symm ▸ hx)
end F6SmallBlockTokenCapacity.TokenRun
