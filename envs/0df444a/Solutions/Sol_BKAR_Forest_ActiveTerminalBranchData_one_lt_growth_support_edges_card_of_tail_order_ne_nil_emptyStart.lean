-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:14.850803+00:00
-- url     : https://prove2.me/submissions/7d03d3ea-1221-4efe-9e4b-cb6c746967f7

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_length_eq_card_support_edges_emptyStart
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
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (htail : (data.tail e).order ≠ []) :
    1 < (data.growth e).support.edges.card := by
  have hlen :
      (e.val :: (data.tail e).order).length =
        (data.growth e).support.edges.card :=
    data.growth_order_length_eq_card_support_edges_emptyStart e rfl
  cases horder : (data.tail e).order with
  | nil =>
      exact False.elim (htail horder)
  | cons a tail =>
      rw [horder, List.length_cons, List.length_cons] at hlen
      rw [← hlen]
      exact Nat.succ_lt_succ (Nat.zero_lt_succ tail.length)
end BKAR.Forest.ActiveTerminalBranchData
