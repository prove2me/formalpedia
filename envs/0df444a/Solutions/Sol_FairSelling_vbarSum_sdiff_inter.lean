-- Prove2me | solution 1 for FairSelling.vbarSum_sdiff_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:15.21103+00:00
-- url     : https://prove2.me/submissions/0cb3211c-2f78-429a-a67d-796c489bf20f

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (Y X : Finset G) :
    vbarSum w p (Y \ X) = vbarSum w p Y - vbarSum w p (Y ∩ X) := by
  have h : Y \ X = Y \ (Y ∩ X) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [h, vbarSum_sdiff w p Finset.inter_subset_left]
end FairSelling
