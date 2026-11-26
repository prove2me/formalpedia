-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.tailForest_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:59.12605+00:00
-- url     : https://prove2.me/submissions/01a991dd-3156-4a64-b293-dcf1ca2e3798

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F (e :: order) G) :
    h.tailForest.edges = insert e F.edges :=
  h.firstStep.edges_eq
end BKAR.Forest.OrderedGrowth
