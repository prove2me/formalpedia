-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growthOrderTail_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:03.23158+00:00
-- url     : https://prove2.me/submissions/43b6bc9f-4040-47bc-87c6-738c5d12029b

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth

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
    (data.growthOrderTail e).1.val = e.val :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
