-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.order_mem_edgeOrders_of_initial_edges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:26.475795+00:00
-- url     : https://prove2.me/submissions/7c78d549-7ae2-42ed-9acc-6471d8b36a02

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_nodup
import Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_TerminalGrowth_order_nodup
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff_toFinset_eq_and_nodup


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.order ∈ data.terminal.edgeOrders := by
  rw [data.terminal.mem_edgeOrders_iff_toFinset_eq_and_nodup]
  exact ⟨(data.edges_eq_toFinset_of_initial_edges_eq_empty hF).symm,
    data.order_nodup⟩
end BKAR.Forest.TerminalGrowth
