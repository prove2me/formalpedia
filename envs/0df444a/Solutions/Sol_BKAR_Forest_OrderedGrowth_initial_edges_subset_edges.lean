-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.initial_edges_subset_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:15.383028+00:00
-- url     : https://prove2.me/submissions/bcdffe96-92b5-42e6-a00a-a270d1d589ce

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_OrderedGrowth_edges_eq_toFinset_union

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G) :
    F.edges ⊆ G.edges := by
  intro e he
  rw [h.edges_eq_toFinset_union]
  exact Finset.mem_union_right order.toFinset he
end BKAR.Forest.OrderedGrowth
