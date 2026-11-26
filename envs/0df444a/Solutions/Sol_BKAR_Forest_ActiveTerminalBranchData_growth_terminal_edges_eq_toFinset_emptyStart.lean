-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_terminal_edges_eq_toFinset_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:17.211589+00:00
-- url     : https://prove2.me/submissions/6343e62c-48e0-44ae-b641-14fb136af296

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_terminal_edges_eq_toFinset_emptyStart
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
    (data.growth e).terminal.edges =
      (e.val :: (data.tail e).order).toFinset :=
  (data.growth e).terminal_edges_eq_toFinset_emptyStart
end BKAR.Forest.ActiveTerminalBranchData
