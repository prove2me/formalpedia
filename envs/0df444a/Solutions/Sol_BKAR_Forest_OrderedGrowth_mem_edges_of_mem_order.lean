-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.mem_edges_of_mem_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:36:40.212156+00:00
-- url     : https://prove2.me/submissions/a73fdaab-136e-420d-99a6-0a771bffb8df

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_subset_edges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G) {e : Edge V}
    (he : e ∈ order) :
    e ∈ G.edges :=
  h.order_toFinset_subset_edges (List.mem_toFinset.mpr he)
end BKAR.Forest.OrderedGrowth
