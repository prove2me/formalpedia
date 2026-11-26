-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.order_toFinset_subset_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:35:50.834635+00:00
-- url     : https://prove2.me/submissions/ea4b3085-c7f0-4c66-a758-04a91dc73c3b

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
    order.toFinset ⊆ G.edges := by
  intro e he
  rw [h.edges_eq_toFinset_union]
  exact Finset.mem_union_left F.edges he
end BKAR.Forest.OrderedGrowth
