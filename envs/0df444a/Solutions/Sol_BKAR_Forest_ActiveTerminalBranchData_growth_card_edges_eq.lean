-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_card_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:02.725471+00:00
-- url     : https://prove2.me/submissions/51e889a8-ec02-4c78-826a-ee65ea6c827d

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_card_edges_eq
import Theorems.Thm_BKAR_Forest_OrderedGrowth_card_edges_eq
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
    (data.growth e).terminal.edges.card =
      F.edges.card + (e.val :: (data.tail e).order).length :=
  (data.growth e).card_edges_eq
end BKAR.Forest.ActiveTerminalBranchData
