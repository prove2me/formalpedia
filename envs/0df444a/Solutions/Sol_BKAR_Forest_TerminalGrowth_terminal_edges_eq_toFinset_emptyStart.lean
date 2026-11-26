-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.terminal_edges_eq_toFinset_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:22:33.821796+00:00
-- url     : https://prove2.me/submissions/b477cb62-6662-40e8-a43d-c2c5081e89a8

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_empty_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth (Forest.empty V)) :
    data.terminal.edges = data.order.toFinset :=
  data.edges_eq_toFinset_of_initial_edges_eq_empty (Forest.empty_edges V)
end BKAR.Forest.TerminalGrowth
