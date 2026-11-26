-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.order_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:36:40.625631+00:00
-- url     : https://prove2.me/submissions/aab50de0-02d0-4a6e-9da4-66622895558b

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_disjoint_initial_edges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G) :
    order.Nodup := by
  induction h with
  | nil F =>
      exact List.nodup_nil
  | cons step tail ih =>
      apply List.Nodup.cons
      · intro he
        have hdisj := tail.order_toFinset_disjoint_initial_edges
        rw [Finset.disjoint_left] at hdisj
        exact hdisj (List.mem_toFinset.mpr he) (by
          rw [step.edges_eq]
          exact Finset.mem_insert_self _ _)
      · exact ih
end BKAR.Forest.OrderedGrowth
