-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.order_mem_edgeOrders_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:51:31.002956+00:00
-- url     : https://prove2.me/submissions/37d46de3-e71b-4f27-b06c-cb5f7901a0e9

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_TerminalGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_empty_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth (Forest.empty V)) :
    data.order ∈ data.terminal.edgeOrders :=
  data.order_mem_edgeOrders_of_initial_edges_eq_empty (Forest.empty_edges V)
end BKAR.Forest.TerminalGrowth
