-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.orderTail_mem_edgeSetOrderTails_of_order_eq_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:28.890016+00:00
-- url     : https://prove2.me/submissions/1e8562b4-b3bc-4fa0-b603-5160deb18a59

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_emptyStart
import Theorems.Thm_BKAR_Forest_TerminalGrowth_order_mem_edgeOrders_emptyStart
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrderTails_iff


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
    ∃ he : e ∈ data.terminal.edges,
      (⟨⟨e, he⟩, order⟩ :
        Σ _ : {x : Edge V // x ∈ data.terminal.edges},
          List (Edge V)) ∈
          edgeSetOrderTails data.terminal.edges := by
  have hmem : e :: order ∈ data.terminal.edgeOrders := by
    rw [← horder]
    exact data.order_mem_edgeOrders_emptyStart
  have hsplit := (cons_mem_edgeOrders_iff data.terminal).mp hmem
  refine ⟨hsplit.1, ?_⟩
  rw [mem_edgeSetOrderTails_iff]
  exact hsplit.2
end BKAR.Forest.TerminalGrowth
