-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:31.150732+00:00
-- url     : https://prove2.me/submissions/270dad3f-5a78-4c69-94ad-e02028f251a9

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_of_initial_edges_eq_empty
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
    data.support.edges = data.order.toFinset :=
  data.support_edges_eq_toFinset_of_initial_edges_eq_empty
    (Forest.empty_edges V)
end BKAR.Forest.TerminalGrowth
