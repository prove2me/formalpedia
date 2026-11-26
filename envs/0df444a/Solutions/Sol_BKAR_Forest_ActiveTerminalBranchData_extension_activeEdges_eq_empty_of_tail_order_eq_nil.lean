-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.extension_activeEdges_eq_empty_of_tail_order_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:24:19.797807+00:00
-- url     : https://prove2.me/submissions/5dcfc012-1340-47fa-aac5-60e0625ddf5c

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_terminal_eq_initial_of_order_eq_nil
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
    (data.extension e).forest.activeEdges = ∅ := by
  rw [← (data.tail e).terminal_eq_initial_of_order_eq_nil htail]
  exact (data.tail e).terminal_activeEdges_eq_empty
end BKAR.Forest.ActiveTerminalBranchData
