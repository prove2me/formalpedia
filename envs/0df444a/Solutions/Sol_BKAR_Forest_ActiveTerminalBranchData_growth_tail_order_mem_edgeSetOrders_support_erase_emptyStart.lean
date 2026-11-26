-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_tail_order_mem_edgeSetOrders_support_erase_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:00.331996+00:00
-- url     : https://prove2.me/submissions/5046a795-abcd-4857-91dc-f867ffa62dba

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart
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
    (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val) :=
  ((data.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart e I).mp
    hsupport).2
end BKAR.Forest.ActiveTerminalBranchData
