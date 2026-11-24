-- Prove2me | solution 1 for FairSelling.optionGoods_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:05:08.489978+00:00
-- url     : https://prove2.me/submissions/24cba97d-8b1e-47b6-9e85-c0247516704e

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
theorem _root_.solution {s t : Finset (Option G)} (h : Disjoint s t) :
    Disjoint (optionGoods s) (optionGoods t) := by
  simp_all +decide [ Finset.disjoint_left, mem_optionGoods ]
end FairSelling
