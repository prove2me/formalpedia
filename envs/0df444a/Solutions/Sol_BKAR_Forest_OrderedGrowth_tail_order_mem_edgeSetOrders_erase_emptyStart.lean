-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.tail_order_mem_edgeSetOrders_erase_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:22.746554+00:00
-- url     : https://prove2.me/submissions/fc664744-c755-4941-8441-39632022d11f

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
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
    {e : Edge V} (h : OrderedGrowth (Forest.empty V) (e :: order) G) :
    order ∈ edgeSetOrders (G.edges.erase e) :=
  h.tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
    (Forest.empty_edges V)
end BKAR.Forest.OrderedGrowth
