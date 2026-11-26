-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:22:14.162414+00:00
-- url     : https://prove2.me/submissions/a6d21235-4040-4d3e-9852-4f6e509c5f0b

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_OrderedGrowth_edges_eq_toFinset_union


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    data.support.edges = data.order.toFinset ∪ F.edges :=
  data.edges_eq_toFinset_union
end BKAR.Forest.TerminalGrowth
