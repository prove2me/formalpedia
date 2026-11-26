-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:30.716929+00:00
-- url     : https://prove2.me/submissions/f50bd0d2-f718-4690-b43c-76d0d8aa0ed3

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
    (data.growthOrderTail e).1.val :: (data.growthOrderTail e).2 =
      e.val :: (data.tail e).order :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
