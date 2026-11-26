-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_order_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:30:11.093289+00:00
-- url     : https://prove2.me/submissions/4c3addab-c6e8-4073-9d39-f119e7163da8

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_def
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_iff_order_toFinset_eq_emptyStart
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


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
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (e.val :: (data.tail e).order).toFinset = I.edges))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e => (e.val :: (data.tail e).order).toFinset = I.edges) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr_right
      (fun _ => data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I)
  rw [data.supportContribution_def I ρ, hfilter]
end BKAR.Forest.ActiveTerminalBranchData
