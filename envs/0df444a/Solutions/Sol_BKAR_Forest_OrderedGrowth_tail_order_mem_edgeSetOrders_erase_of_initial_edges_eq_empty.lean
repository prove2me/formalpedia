-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:26:40.945815+00:00
-- url     : https://prove2.me/submissions/62cdab36-64ed-4548-82d2-d4765782242f

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    {e : Edge V} (h : OrderedGrowth F (e :: order) G) (hF : F.edges = ∅) :
    order ∈ edgeSetOrders (G.edges.erase e) :=
  ((cons_mem_edgeOrders_iff G).mp
    (h.order_mem_edgeOrders_of_initial_edges_eq_empty hF)).2
end BKAR.Forest.OrderedGrowth
