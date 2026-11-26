-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_mem_edgeSetOrderTails_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:08.417189+00:00
-- url     : https://prove2.me/submissions/bf62a23a-6183-4aac-8620-68ecadfd8deb

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrderTails_iff


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
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    data.growthOrderTail e ∈
      edgeSetOrderTails (data.growth e).terminal.edges := by
  rw [growthOrderTail, mem_edgeSetOrderTails_iff]
  exact ((cons_mem_edgeOrders_iff (data.growth e).terminal).mp
    (data.growth_order_mem_edgeOrders_emptyStart e)).2
end BKAR.Forest.ActiveTerminalBranchData
