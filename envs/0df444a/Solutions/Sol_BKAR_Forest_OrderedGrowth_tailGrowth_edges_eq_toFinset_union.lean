-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.tailGrowth_edges_eq_toFinset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:34.324109+00:00
-- url     : https://prove2.me/submissions/4c76d325-87eb-4440-a75c-b80dd680b76a

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
theorem _root_.solution
    (h : OrderedGrowth F (e :: order) G) :
    G.edges = order.toFinset ∪ h.tailForest.edges :=
  h.tailGrowth.edges_eq_toFinset_union
end BKAR.Forest.OrderedGrowth
