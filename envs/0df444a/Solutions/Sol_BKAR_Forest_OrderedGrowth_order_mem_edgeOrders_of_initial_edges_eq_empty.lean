-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.order_mem_edgeOrders_of_initial_edges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:06.980828+00:00
-- url     : https://prove2.me/submissions/d24721cd-7155-4e3f-8c6d-14cf944d4297

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_nodup
import Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_TerminalGrowth_order_nodup
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff_toFinset_eq_and_nodup


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    (h : OrderedGrowth F order G) (hF : F.edges = ∅) :
    order ∈ G.edgeOrders := by
  rw [G.mem_edgeOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [h.edges_eq_toFinset_union, hF]
    rw [Finset.union_empty]
  · exact h.order_nodup
end BKAR.Forest.OrderedGrowth
