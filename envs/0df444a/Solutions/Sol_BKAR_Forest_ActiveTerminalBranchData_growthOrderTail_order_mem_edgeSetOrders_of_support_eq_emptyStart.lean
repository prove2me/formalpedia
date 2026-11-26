-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:07.164822+00:00
-- url     : https://prove2.me/submissions/0a19f0ff-f6d8-41e7-8260-c31eba510b74

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_mem_edgeSetOrders_of_support_eq_emptyStart
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrderTail_order


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
    ((data.growthOrderTail e).1.val :: (data.growthOrderTail e).2) ∈
      edgeSetOrders I.edges := by
  rw [data.growthOrderTail_order e]
  exact data.growth_order_mem_edgeSetOrders_of_support_eq_emptyStart e
    hsupport
end BKAR.Forest.ActiveTerminalBranchData
