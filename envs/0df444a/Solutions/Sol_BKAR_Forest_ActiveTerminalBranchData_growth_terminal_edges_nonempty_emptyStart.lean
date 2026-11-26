-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_terminal_edges_nonempty_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:44.851378+00:00
-- url     : https://prove2.me/submissions/d93a93cb-dbcb-45c0-8af0-5fcc84f8a5ed

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff


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
    (data.growth e).terminal.edges.Nonempty := by
  have hsplit :=
    (cons_mem_edgeOrders_iff (data.growth e).terminal).mp
      (data.growth_order_mem_edgeOrders_emptyStart e)
  exact ⟨e.val, hsplit.1⟩
end BKAR.Forest.ActiveTerminalBranchData
