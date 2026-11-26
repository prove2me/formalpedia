-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_of_initial_edges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:22:30.447083+00:00
-- url     : https://prove2.me/submissions/88ffa62f-87c9-45dc-901f-b651b935bc36

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges
import Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges
import Theorems.Thm_BKAR_Forest_support_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.support.edges = data.order.toFinset := by
  rw [data.support_edges, data.edges_eq_toFinset_of_initial_edges_eq_empty hF]
end BKAR.Forest.TerminalGrowth
