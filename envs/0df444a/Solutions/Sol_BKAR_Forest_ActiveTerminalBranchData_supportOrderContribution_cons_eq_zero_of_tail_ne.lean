-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_zero_of_tail_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:06.203584+00:00
-- url     : https://prove2.me/submissions/65f89f98-5b23-4a08-b8c4-94e5a8fabc9c

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_eq
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_def
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
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (htail : (data.tail (emptyActiveEdge a)).order ≠ tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ = 0 := by
  rw [data.supportOrderContribution_def I (a :: tail) ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    have heq : e = emptyActiveEdge a := by
      apply Subtype.ext
      have horder := h.2
      rw [data.growthOrder_eq e] at horder
      injection horder with hfirst _
    apply htail
    have horder := h.2
    rw [data.growthOrder_eq e] at horder
    injection horder with _ htail_eq
    rw [← heq]
    exact htail_eq
end BKAR.Forest.ActiveTerminalBranchData
