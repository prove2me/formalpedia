-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.support_edges_eq_toFinset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:20.514797+00:00
-- url     : https://prove2.me/submissions/c318a3f3-4b9e-4682-9e14-4a2b28512ff7

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
    h.support.edges = order.toFinset ∪ F.edges :=
  h.edges_eq_toFinset_union
end BKAR.Forest.OrderedGrowth
