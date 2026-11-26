-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:30.724805+00:00
-- url     : https://prove2.me/submissions/2fbeaea0-d4c2-4e46-a10a-66ac825ec603

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
theorem _root_.solution (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).terminal = (data.tail e).terminal :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
