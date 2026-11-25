-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_INCIDENCE_EQUALITY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:48:59.726727+00:00
-- url     : https://prove2.me/submissions/1e35fa8a-9dd7-48b3-a9a7-11d3cab0187c

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_three_incidence_equality

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (hB : Fintype.card B ≤ 3) (hq : 3 ≤ q) :
    Fintype.card B = 3 ∧
    (∀ i : Fin 3, ((R.firstSteps 3 hq).support i).card = 2) ∧
    (∀ b : B, ((R.firstSteps 3 hq).participationSteps b).card = 2) :=
  three_incidence_equality (R.firstSteps 3 hq) hB
end F6SmallBlockTokenCapacity.TokenRun
