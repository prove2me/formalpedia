-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.order_toFinset_disjoint_initial_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:22.732044+00:00
-- url     : https://prove2.me/submissions/c6d09c9b-4a0b-40c1-86fd-27f889d40052

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_disjoint_initial_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    Disjoint data.order.toFinset F.edges :=
  data.growth.order_toFinset_disjoint_initial_edges
end BKAR.Forest.TerminalGrowth
