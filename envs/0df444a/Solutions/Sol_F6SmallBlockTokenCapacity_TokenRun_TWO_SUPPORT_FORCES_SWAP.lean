-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.TWO_SUPPORT_FORCES_SWAP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:42:27.449872+00:00
-- url     : https://prove2.me/submissions/28b97855-3f1f-4a41-ae13-7aebf1666274

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_named_pair_swap

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (i : Fin q) (hcard : (R.support i).card = 2) :
    ∃ x y : B, x ≠ y ∧ R.support i = {x, y} ∧
      R.state i.succ x = R.state i.castSucc y ∧
      R.state i.succ y = R.state i.castSucc x := by
  classical
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
  exact ⟨x, y, hxy, hs, R.named_pair_swap i x y hxy hs⟩
end F6SmallBlockTokenCapacity.TokenRun
