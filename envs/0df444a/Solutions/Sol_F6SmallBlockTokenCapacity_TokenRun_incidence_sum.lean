-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.incidence_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:25:47.942231+00:00
-- url     : https://prove2.me/submissions/da7b1e3d-e570-4795-a4b7-03e272dc334f

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
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (T : Finset (Fin q)) :
    (∑ i ∈ T, (R.support i).card) =
      ∑ b : B, (T.filter (fun i => b ∈ R.support i)).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp
end F6SmallBlockTokenCapacity.TokenRun
