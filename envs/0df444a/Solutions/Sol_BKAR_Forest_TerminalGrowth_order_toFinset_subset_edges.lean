-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.order_toFinset_subset_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:09.750219+00:00
-- url     : https://prove2.me/submissions/3500a419-dad2-42a6-91cc-972e65f41d0e

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_subset_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    data.order.toFinset ⊆ data.terminal.edges :=
  data.growth.order_toFinset_subset_edges
end BKAR.Forest.TerminalGrowth
