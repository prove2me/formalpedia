-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.pair_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:26:58.929914+00:00
-- url     : https://prove2.me/submissions/24981149-bf0d-40ef-a292-2e4deb8abfc7

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_previous_holder_mem
attribute [local simp] F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps

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
    (hout : ∀ b, b ∉ s → before b = after b)
    (hmove : ∀ b, b ∈ s → before b ≠ after b)
    (x y : B) (_hxy : x ≠ y) (hs : s = {x, y}) :
    after x = before y ∧ after y = before x := by
  classical
  have hone (a c : B) (ha : a ∈ s) (hac : s = {a, c}) : after a = before c := by
    have hmem := previous_holder_mem s before after hout ha
    rw [hac, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with heq | heq
    · have hsame : before a = after a := by
        calc
          before a = before (before.symm (after a)) := congrArg before heq.symm
          _ = after a := before.apply_symm_apply _
      exact (hmove a ha hsame).elim
    · rw [← heq, before.apply_symm_apply]
  constructor
  · exact hone x y (by simp [hs]) hs
  · exact hone y x (by simp [hs]) (by simpa [Finset.pair_comm] using hs)
end F6SmallBlockTokenCapacity.TokenRun
