-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_extension_support_of_tail_order_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:31.524378+00:00
-- url     : https://prove2.me/submissions/fb65fa30-f75b-4109-896f-29ffc0e8b572

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_eq_initial_support_of_order_eq_nil
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
    (e : {e // e ∈ F.activeEdges})
    (htail : (data.tail e).order = []) :
    (data.growth e).support = (data.extension e).forest.support := by
  change (data.tail e).support = (data.extension e).forest.support
  exact (data.tail e).support_eq_initial_support_of_order_eq_nil htail
end BKAR.Forest.ActiveTerminalBranchData
