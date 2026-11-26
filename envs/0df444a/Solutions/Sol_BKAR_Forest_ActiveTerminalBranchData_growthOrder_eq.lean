-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growthOrder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:53:04.156399+00:00
-- url     : https://prove2.me/submissions/442d69f8-d651-4efd-8319-c84c417bf3c1

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
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
    data.growthOrder e = e.val :: (data.tail e).order :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
