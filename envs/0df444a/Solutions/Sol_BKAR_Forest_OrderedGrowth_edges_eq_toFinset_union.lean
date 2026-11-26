-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.edges_eq_toFinset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:27:26.928872+00:00
-- url     : https://prove2.me/submissions/946ed430-9688-4ad3-9c89-7439f18c301c

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G) :
    G.edges = order.toFinset ∪ F.edges := by
  induction h with
  | nil F =>
      rw [List.toFinset_nil, Finset.empty_union]
  | cons step tail ih =>
      rw [ih, step.edges_eq, List.toFinset_cons]
      rw [Finset.union_insert, Finset.insert_union]
end BKAR.Forest.OrderedGrowth
