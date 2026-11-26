-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:17.907959+00:00
-- url     : https://prove2.me/submissions/5679405d-7b8b-4b14-ae73-f244fce04e21

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart

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
    data.growthOrder e ∈ edgeSetOrders I.edges :=
  data.growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart e
    hsupport
end BKAR.Forest.ActiveTerminalBranchData
