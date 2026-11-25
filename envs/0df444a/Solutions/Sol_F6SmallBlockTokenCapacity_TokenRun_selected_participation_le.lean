-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.selected_participation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:38:07.547893+00:00
-- url     : https://prove2.me/submissions/8d669548-cfb5-4011-898d-8cd6a199059b

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_participation_count
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
theorem _root_.solution (T : Finset (Fin q)) (b : B) :
    (T.filter (fun i => b ∈ R.support i)).card ≤ Fintype.card B - 1 := by
  classical
  apply le_trans (Finset.card_le_card ?_) (R.participation_count b)
  intro i hi
  exact (R.mem_participationSteps b i).mpr (Finset.mem_filter.mp hi).2
end F6SmallBlockTokenCapacity.TokenRun
