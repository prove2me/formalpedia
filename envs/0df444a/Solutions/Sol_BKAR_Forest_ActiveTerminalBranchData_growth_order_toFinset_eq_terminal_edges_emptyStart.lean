-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_order_toFinset_eq_terminal_edges_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:38.699187+00:00
-- url     : https://prove2.me/submissions/8be8a39f-4bfa-4d83-b053-2e1882675737

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_terminal_edges_eq_toFinset_emptyStart
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
    (e.val :: (data.tail e).order).toFinset =
      (data.growth e).terminal.edges :=
  (data.growth_terminal_edges_eq_toFinset_emptyStart e).symm
end BKAR.Forest.ActiveTerminalBranchData
