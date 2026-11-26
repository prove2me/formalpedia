-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_order_length_eq_card_support_edges_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:04.813405+00:00
-- url     : https://prove2.me/submissions/533bf125-d10e-4024-ac97-b2138258d5a7

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_mem_edgeSetOrders_of_support_eq_emptyStart
import Theorems.Thm_BKAR_Forest_length_eq_card_of_mem_edgeSetOrders
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
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (e.val :: (data.tail e).order).length = I.edges.card :=
  length_eq_card_of_mem_edgeSetOrders
    (data.growth_order_mem_edgeSetOrders_of_support_eq_emptyStart e
      hsupport)
end BKAR.Forest.ActiveTerminalBranchData
