-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.tail_order_eq_nil_iff_growth_support_eq_singleton_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:12.099996+00:00
-- url     : https://prove2.me/submissions/7166a56e-1541-41ec-a163-82f4b0ce5f12

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_singleton_iff_emptyStart
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
    (data.tail e).order = [] ↔
      (data.growth e).support = ForestIndex.singleton e.val := by
  constructor
  · intro htail
    exact (data.growth_support_eq_singleton_iff_emptyStart e e.val).mpr
      ⟨rfl, htail⟩
  · intro hsupport
    exact
      ((data.growth_support_eq_singleton_iff_emptyStart e e.val).mp
        hsupport).2
end BKAR.Forest.ActiveTerminalBranchData
