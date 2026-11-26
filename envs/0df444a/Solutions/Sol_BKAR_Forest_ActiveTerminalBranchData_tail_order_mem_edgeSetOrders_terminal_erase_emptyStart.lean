-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.tail_order_mem_edgeSetOrders_terminal_erase_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:52.24864+00:00
-- url     : https://prove2.me/submissions/5ff789ea-02b7-4abc-b8bb-b3245898c107

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff
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
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.tail e).order ∈
      edgeSetOrders ((data.growth e).terminal.edges.erase e.val) :=
  ((cons_mem_edgeOrders_iff (data.growth e).terminal).mp
    (data.growth_order_mem_edgeOrders_emptyStart e)).2
end BKAR.Forest.ActiveTerminalBranchData
