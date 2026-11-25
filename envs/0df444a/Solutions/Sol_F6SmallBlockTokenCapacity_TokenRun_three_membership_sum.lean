-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.three_membership_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:22:23.394664+00:00
-- url     : https://prove2.me/submissions/0f0ae731-c5f3-4f3d-bd5f-14be7da63f00

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
theorem _root_.solution (S : Fin 3 → Finset B) (b : B) :
    ((Finset.univ : Finset (Fin 3)).filter (fun i => b ∈ S i)).card =
      (if b ∈ S 0 then 1 else 0) + (if b ∈ S 1 then 1 else 0) +
        (if b ∈ S 2 then 1 else 0) := by
  classical
  rw [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [add_assoc]
end F6SmallBlockTokenCapacity.TokenRun
