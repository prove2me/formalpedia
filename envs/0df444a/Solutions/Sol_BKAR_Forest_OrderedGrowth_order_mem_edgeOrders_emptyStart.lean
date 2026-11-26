-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.order_mem_edgeOrders_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:51:17.1808+00:00
-- url     : https://prove2.me/submissions/f4bdfb4f-1bbd-4621-a6ec-853b3c69918c

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_empty_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    (h : OrderedGrowth (Forest.empty V) order G) :
    order ∈ G.edgeOrders :=
  h.order_mem_edgeOrders_of_initial_edges_eq_empty (Forest.empty_edges V)
end BKAR.Forest.OrderedGrowth
