-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:13.778448+00:00
-- url     : https://prove2.me/submissions/690ed83b-ead1-4496-899b-c2c993ecfd0c

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
    (data.growth e).order = e.val :: (data.tail e).order :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
