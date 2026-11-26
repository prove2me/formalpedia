-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.initial_edges_subset_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:13.562941+00:00
-- url     : https://prove2.me/submissions/2f8c2ad4-5f8a-4a0b-93bb-e23d7f7afa2f

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_initial_edges_subset_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    F.edges ⊆ data.terminal.edges :=
  data.growth.initial_edges_subset_edges
end BKAR.Forest.TerminalGrowth
