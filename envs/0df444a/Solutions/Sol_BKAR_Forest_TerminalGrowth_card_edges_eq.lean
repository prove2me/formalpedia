-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.card_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:14.90291+00:00
-- url     : https://prove2.me/submissions/1bdc464c-7beb-42d0-86c2-ece9001e3e34

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_card_edges_eq


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    data.terminal.edges.card = F.edges.card + data.order.length :=
  data.growth.card_edges_eq
end BKAR.Forest.TerminalGrowth
