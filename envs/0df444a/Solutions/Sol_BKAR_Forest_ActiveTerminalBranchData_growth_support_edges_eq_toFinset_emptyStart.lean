-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_support_edges_eq_toFinset_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:31.06304+00:00
-- url     : https://prove2.me/submissions/3027fd4c-7545-4d1b-ad43-e6f78ad6cf6b

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_emptyStart
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
    (data.growth e).support.edges =
      (e.val :: (data.tail e).order).toFinset :=
  (data.growth e).support_edges_eq_toFinset_emptyStart
end BKAR.Forest.ActiveTerminalBranchData
