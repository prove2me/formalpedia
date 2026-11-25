-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.SMALL_BLOCK_TOKEN_CAPACITIES
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:02:25.502234+00:00
-- url     : https://prove2.me/submissions/f99b14ce-8dd5-409b-8639-5698af1344d7

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_TWO_SITE_CAPACITY
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_THREE_SITE_CAPACITY

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (R : TokenRun B W q) :
    (Fintype.card B ≤ 2 → q ≤ 1) ∧ (Fintype.card B ≤ 3 → q ≤ 2) :=
  ⟨R.TWO_SITE_CAPACITY, R.THREE_SITE_CAPACITY⟩
end F6SmallBlockTokenCapacity.TokenRun
