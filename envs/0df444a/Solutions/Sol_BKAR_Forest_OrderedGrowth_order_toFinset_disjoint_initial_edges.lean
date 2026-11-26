-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.order_toFinset_disjoint_initial_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:35:53.871794+00:00
-- url     : https://prove2.me/submissions/8b866611-d2e9-4ea6-9658-e4c148163e15

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
    Disjoint order.toFinset F.edges := by
  induction h with
  | nil F =>
      rw [List.toFinset_nil]
      exact Finset.disjoint_empty_left F.edges
  | cons step tail ih =>
      rw [List.toFinset_cons, Finset.disjoint_insert_left]
      constructor
      · exact step.new_not_mem
      · rw [Finset.disjoint_left] at ih ⊢
        intro x hx hxF
        exact ih hx (by
          rw [step.edges_eq]
          exact Finset.mem_insert_of_mem hxF)
end BKAR.Forest.OrderedGrowth
