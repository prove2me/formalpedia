-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.mem_edges_of_mem_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:19.122128+00:00
-- url     : https://prove2.me/submissions/7e11512d-a8f9-4d82-9a70-54624f9d67f7

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) {e : Edge V}
    (he : e ∈ data.order) :
    e ∈ data.terminal.edges :=
  data.growth.mem_edges_of_mem_order he
end BKAR.Forest.TerminalGrowth
