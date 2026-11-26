-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_iff_order_toFinset_eq_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:54.489299+00:00
-- url     : https://prove2.me/submissions/71cda4b4-0bae-47d4-a860-9bcc0d5c3a1f

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_edges_eq_toFinset_emptyStart
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
    (I : ForestIndex V) :
    (data.growth e).support = I ↔
      (e.val :: (data.tail e).order).toFinset = I.edges := by
  constructor
  · intro h
    rw [← data.growth_support_edges_eq_toFinset_emptyStart e]
    rw [h]
  · intro h
    apply ForestIndex.ext
    rw [data.growth_support_edges_eq_toFinset_emptyStart e, h]
end BKAR.Forest.ActiveTerminalBranchData
