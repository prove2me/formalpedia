-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_first_mem_support_edges_of_support_eq_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:17.243689+00:00
-- url     : https://prove2.me/submissions/552e4406-7846-4359-aaaa-fb49b8e712ca

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart

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
    e.val ∈ I.edges :=
  ((data.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart e I).mp
    hsupport).1
end BKAR.Forest.ActiveTerminalBranchData
