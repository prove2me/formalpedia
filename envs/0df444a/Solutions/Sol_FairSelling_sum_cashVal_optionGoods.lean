-- Prove2me | solution 1 for FairSelling.sum_cashVal_optionGoods
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:40.424125+00:00
-- url     : https://prove2.me/submissions/f2766391-4930-42df-a7c1-892aa8201fed

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.mem_optionGoods

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (R : Finset G) (w : G → ℝ) (s : Finset (Option G)) :
    ∑ g ∈ optionGoods s, restrictVal R w g = ∑ x ∈ s, cashVal R w x := by
  induction' s using Finset.induction with x s hx ih;
  · rfl;
  · cases x <;> simp_all +decide [ Finset.sum_insert hx ];
    · rw [ ← ih, show optionGoods ( insert none s ) = optionGoods s from by ext; simp +decide [ hx ] ];
    · rw [ ← ih, show optionGoods ( insert ( some _ ) s ) = { ‹_› } ∪ optionGoods s from ?_ ];
      · rw [ Finset.sum_union ] <;> simp +decide [ hx ];
      · ext; simp [optionGoods]
end FairSelling
