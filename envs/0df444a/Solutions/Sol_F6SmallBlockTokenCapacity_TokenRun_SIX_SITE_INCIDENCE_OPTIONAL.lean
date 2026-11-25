-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.SIX_SITE_INCIDENCE_OPTIONAL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:41:48.77282+00:00
-- url     : https://prove2.me/submissions/7954ae1b-8c0a-4182-9026-7270c5867dfa

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_incidence_bounds

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (R : TokenRun B W q) (hB : Fintype.card B ≤ 6) :
    2 * q ≤ 6 * 5 ∧ q ≤ 15 := by
  have hcap : Fintype.card B * (Fintype.card B - 1) ≤ 6 * 5 :=
    Nat.mul_le_mul hB (by omega)
  have hinc : 2 * q ≤ 6 * 5 := R.incidence_bounds.1.trans (R.incidence_bounds.2.trans hcap)
  exact ⟨hinc, by omega⟩
end F6SmallBlockTokenCapacity.TokenRun
