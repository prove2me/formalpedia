-- Prove2me | solution 1 for FairSelling.sum_cashPrice_optionGoods
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:33.100891+00:00
-- url     : https://prove2.me/submissions/f253d7cd-b7b3-4d3d-97dd-482c67dc2c50

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
theorem _root_.solution (R : Finset G) (p : G → ℝ) (cash : ℝ)
    (s : Finset (Option G)) :
    (∑ g ∈ optionGoods s, restrictVal R p g) + (if none ∈ s then cash else 0) =
      ∑ x ∈ s, cashPrice R p cash x := by
  induction' s using Finset.induction with x s hx ih <;> simp +decide [ * ];
  · exact Finset.sum_empty;
  · cases x <;> simp +decide [ *, Finset.sum_insert hx ];
    · rw [ add_comm, ← ih ] ; simp +decide [ hx, optionGoods ] ;
    · rw [ ← ih, show optionGoods ( insert ( some _ ) s ) = { ‹_› } ∪ optionGoods s from ?_ ];
      · grind +suggestions;
      · ext; simp [optionGoods]
end FairSelling
