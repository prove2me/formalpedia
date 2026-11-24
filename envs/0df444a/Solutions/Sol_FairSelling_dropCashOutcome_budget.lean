-- Prove2me | solution 1 for FairSelling.dropCashOutcome_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:55.136107+00:00
-- url     : https://prove2.me/submissions/fca6b099-7c51-408c-b635-fd1ac2cc34a3

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_sum_cashPrice_optionGoods
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
    (o : Outcome (Option G) 2) (hcash : 0 ≤ cash)
    (hbudget : ∑ i, o.money i ≤ ∑ x ∈ o.sold, cashPrice R p cash x) :
    ∑ i, (dropCashOutcome o).money i ≤
      (∑ g ∈ (dropCashOutcome o).sold, restrictVal R p g) + cash := by
  refine hbudget.trans ?_
  rw [← sum_cashPrice_optionGoods]
  split_ifs <;> simp [dropCashOutcome, hcash]
end FairSelling
