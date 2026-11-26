-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.edges_eq_toFinset_of_initial_edges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:46.488532+00:00
-- url     : https://prove2.me/submissions/949242f7-d5cc-49fb-9fea-38458b8c6c69

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
theorem _root_.solution
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.terminal.edges = data.order.toFinset := by
  rw [data.edges_eq_toFinset_union, hF]
  rw [Finset.union_empty]
end BKAR.Forest.TerminalGrowth
