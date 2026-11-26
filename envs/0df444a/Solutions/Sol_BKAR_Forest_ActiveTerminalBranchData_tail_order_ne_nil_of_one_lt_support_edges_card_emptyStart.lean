-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:21.263802+00:00
-- url     : https://prove2.me/submissions/847ca70b-0d85-45a6-97bb-7c4072683ce6

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart
import Theorems.Thm_BKAR_ForestIndex_singleton_edges
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
    {I : ForestIndex V} (hsupport : (data.growth e).support = I)
    (hcard : 1 < I.edges.card) :
    (data.tail e).order ≠ [] := by
  apply data.tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart e
  intro hsingleton
  have hI : I = ForestIndex.singleton e.val := by
    rw [← hsupport, hsingleton]
  have hcardI : I.edges.card = 1 := by
    rw [hI, ForestIndex.singleton_edges, Finset.card_singleton]
  rw [hcardI] at hcard
  exact Nat.lt_irrefl 1 hcard
end BKAR.Forest.ActiveTerminalBranchData
