-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.card_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:36:36.136797+00:00
-- url     : https://prove2.me/submissions/f8cb74dd-740e-48ff-a9d6-658016542e4d

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
    G.edges.card = F.edges.card + order.length := by
  induction h with
  | nil F =>
      rw [List.length_nil, Nat.add_zero]
  | cons step tail ih =>
      rw [ih, step.edges_eq, Finset.card_insert_of_notMem step.new_not_mem,
        List.length_cons]
      rw [Nat.add_assoc, Nat.add_comm 1]
end BKAR.Forest.OrderedGrowth
