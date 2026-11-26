-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.edges_eq_toFinset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:47.37588+00:00
-- url     : https://prove2.me/submissions/08bb8af9-b0a1-47ce-a817-7a2c847dd0fa

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
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
    data.terminal.edges = data.order.toFinset ∪ F.edges :=
  data.growth.edges_eq_toFinset_union
end BKAR.Forest.TerminalGrowth
