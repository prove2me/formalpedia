-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:21.932884+00:00
-- url     : https://prove2.me/submissions/c23a7663-1622-41ff-a140-aaf762f5d5d3

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_tail_order_eq_nil_iff_growth_support_eq_singleton_emptyStart
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
    (hsupport :
      (data.growth e).support ≠ ForestIndex.singleton e.val) :
    (data.tail e).order ≠ [] := by
  intro htail
  exact hsupport
    ((data.tail_order_eq_nil_iff_growth_support_eq_singleton_emptyStart e).mp
      htail)
end BKAR.Forest.ActiveTerminalBranchData
