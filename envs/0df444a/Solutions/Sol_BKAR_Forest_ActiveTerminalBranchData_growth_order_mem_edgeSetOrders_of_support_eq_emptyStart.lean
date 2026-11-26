-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_order_mem_edgeSetOrders_of_support_eq_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:58.790066+00:00
-- url     : https://prove2.me/submissions/15efc1d0-67cf-42e8-849b-dc10fb1a6074

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_iff_order_toFinset_eq_emptyStart
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_nodup
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff_toFinset_eq_and_nodup
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
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (e.val :: (data.tail e).order) ∈ edgeSetOrders I.edges := by
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  exact ⟨
    (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I).mp
      hsupport,
    data.growth_order_nodup e⟩
end BKAR.Forest.ActiveTerminalBranchData
