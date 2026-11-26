-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:40.343885+00:00
-- url     : https://prove2.me/submissions/87648858-f835-4545-a3ff-270b9b082482

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_def


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : order ∉ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I order ρ = 0 := by
  rw [data.supportOrderContribution_def I order ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    apply horder
    rw [← h.2]
    exact data.growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart e h.1
end BKAR.Forest.ActiveTerminalBranchData
