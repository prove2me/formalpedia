-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.rank_after_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:13:48.592507+00:00
-- url     : https://prove2.me/submissions/734d17bc-0c8d-4092-a8e8-71d66eff0b10

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_rank_monotone

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (b : B) {i j : Fin q} (hij : i < j)
    (hj : b ∈ R.support j) :
    R.rank b (R.state i.succ b) < R.rank b (R.state j.succ b) := by
  apply lt_of_le_of_lt (R.rank_monotone b (show i.succ ≤ j.castSucc from ?_))
    (R.HWORSE j b hj)
  change i.val + 1 ≤ j.val
  exact hij
end F6SmallBlockTokenCapacity.TokenRun
