-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.named_pair_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:35:30.804923+00:00
-- url     : https://prove2.me/submissions/80acf865-5e83-4ec2-9202-e8eae005fec2

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_pair_swap

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (i : Fin q) (x y : B) (hxy : x ≠ y)
    (hs : R.support i = {x, y}) :
    R.state i.succ x = R.state i.castSucc y ∧
    R.state i.succ y = R.state i.castSucc x := by
  apply pair_swap (R.support i) (R.state i.castSucc) (R.state i.succ)
    (R.HOUT i) ?_ x y hxy hs
  intro b hb heq
  have h := R.HWORSE i b hb
  rw [heq] at h
  exact lt_irrefl _ h
end F6SmallBlockTokenCapacity.TokenRun
