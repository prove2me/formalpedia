-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.tailGrowth_card_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:37.340527+00:00
-- url     : https://prove2.me/submissions/e4ae56e3-0e85-460a-b871-f9447d91b830

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_OrderedGrowth_card_edges_eq

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F (e :: order) G) :
    G.edges.card = h.tailForest.edges.card + order.length :=
  h.tailGrowth.card_edges_eq
end BKAR.Forest.OrderedGrowth
