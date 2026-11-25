-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.initial_rank_lt_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:15:05.291269+00:00
-- url     : https://prove2.me/submissions/be3fe957-8a44-4156-b5c0-f6b5a97845f5

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
theorem _root_.solution (b : B) {i : Fin q} (hi : b ∈ R.support i) :
    R.rank b (R.state 0 b) < R.rank b (R.state i.succ b) :=
  lt_of_le_of_lt (R.rank_monotone b (Fin.zero_le _)) (R.HWORSE i b hi)
end F6SmallBlockTokenCapacity.TokenRun
