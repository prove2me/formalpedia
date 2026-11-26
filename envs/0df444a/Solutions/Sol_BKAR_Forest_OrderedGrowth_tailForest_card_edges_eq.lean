-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.tailForest_card_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:19.185844+00:00
-- url     : https://prove2.me/submissions/517a37f7-de1c-4f1f-80df-2abce7ff8b8f

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
import Theorems.Thm_BKAR_Forest_OrderedGrowth_first_not_mem_edges
import Theorems.Thm_BKAR_Forest_OrderedGrowth_tailForest_edges_eq

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F (e :: order) G) :
    h.tailForest.edges.card = F.edges.card + 1 := by
  rw [h.tailForest_edges_eq]
  exact Finset.card_insert_of_notMem h.first_not_mem_edges
end BKAR.Forest.OrderedGrowth
