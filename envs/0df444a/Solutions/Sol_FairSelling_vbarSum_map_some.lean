-- Prove2me | solution 1 for FairSelling.vbarSum_map_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:06.466167+00:00
-- url     : https://prove2.me/submissions/ac76d698-762b-4249-bf2a-1b0b8ed5569e

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (R : Finset G) (w p : G → ℝ) (c : ℝ) {C : Finset G} (hC : C ⊆ R) :
    vbarSum (cashVal R w) (cashPrice R p c) (C.map Function.Embedding.some)
      = vbarSum w p C := by
  classical
  simp only [vbarSum, Finset.sum_map, Function.Embedding.some_apply, vbar, cashVal_some,
    cashPrice_some]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [restrictVal_mem R w (hC hg), restrictVal_mem R p (hC hg)]
end FairSelling
