-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchData_terminal_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:33.039608+00:00
-- url     : https://prove2.me/submissions/4ff39926-e465-48e1-8c68-70d3f2e7480a

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
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
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.branchData.terminal e).activeEdges = ∅ :=
  (data.tail e).terminal_activeEdges_eq_empty
end BKAR.Forest.ActiveTerminalBranchData
