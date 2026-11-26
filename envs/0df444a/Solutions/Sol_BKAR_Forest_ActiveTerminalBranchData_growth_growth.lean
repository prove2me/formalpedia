-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:33.470886+00:00
-- url     : https://prove2.me/submissions/1a8706f6-9f5f-4c88-8014-374a456bb346

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
    (data.growth e).growth =
      (data.extension e).consGrowth (data.tail e).growth :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
