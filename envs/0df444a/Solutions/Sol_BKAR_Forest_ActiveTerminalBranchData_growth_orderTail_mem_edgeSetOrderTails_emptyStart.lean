-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_orderTail_mem_edgeSetOrderTails_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:00.048497+00:00
-- url     : https://prove2.me/submissions/0fbdea1e-6230-4f9f-9b2f-023d8ae3405e

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrderTails_iff
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    ∃ he : e.val ∈ (data.growth e).terminal.edges,
      (⟨⟨e.val, he⟩, (data.tail e).order⟩ :
        Σ _ : {x : Edge V // x ∈ (data.growth e).terminal.edges},
          List (Edge V)) ∈
        edgeSetOrderTails (data.growth e).terminal.edges := by
  have hsplit :=
    (cons_mem_edgeOrders_iff (data.growth e).terminal).mp
      (data.growth_order_mem_edgeOrders_emptyStart e)
  refine ⟨hsplit.1, ?_⟩
  rw [mem_edgeSetOrderTails_iff]
  exact hsplit.2
end BKAR.Forest.ActiveTerminalBranchData
