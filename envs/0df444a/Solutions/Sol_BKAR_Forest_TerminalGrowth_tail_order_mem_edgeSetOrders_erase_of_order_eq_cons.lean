-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.tail_order_mem_edgeSetOrders_erase_of_order_eq_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:27.183865+00:00
-- url     : https://prove2.me/submissions/65a07093-8260-422d-a9b1-9f8aada528a3

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_emptyStart
import Theorems.Thm_BKAR_Forest_TerminalGrowth_order_mem_edgeOrders_emptyStart
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth (Forest.empty V))
    {e : Edge V} {order : List (Edge V)}
    (horder : data.order = e :: order) :
    order ∈ edgeSetOrders (data.terminal.edges.erase e) := by
  have hmem : e :: order ∈ data.terminal.edgeOrders := by
    rw [← horder]
    exact data.order_mem_edgeOrders_emptyStart
  exact ((cons_mem_edgeOrders_iff data.terminal).mp hmem).2
end BKAR.Forest.TerminalGrowth
