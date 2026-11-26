-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_orderedContribution_of_support_eq_and_tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:18.586366+00:00
-- url     : https://prove2.me/submissions/c045c9bb-444c-4727-a2a3-00308207a92d

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_eq
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_def
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
attribute [local simp] BKAR.Forest.emptyActiveEdge_val



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
    (hsupport : (data.growth (emptyActiveEdge a)).support = I)
    (htail : (data.tail (emptyActiveEdge a)).order = tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ =
      (data.growth (emptyActiveEdge a)).terminal.orderedContribution
        (a :: tail) ρ := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I ∧
            data.growthOrder e = a :: tail) =
        {emptyActiveEdge a} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      apply Subtype.ext
      have horder := h.2.2
      rw [data.growthOrder_eq e] at horder
      injection horder with hfirst _
    · intro h
      rw [h]
      constructor
      · exact Finset.mem_attach _ _
      · constructor
        · exact hsupport
        · rw [data.growthOrder_eq (emptyActiveEdge a), htail,
            emptyActiveEdge_val]
  rw [data.supportOrderContribution_def I (a :: tail) ρ]
  rw [hfilter, Finset.sum_singleton]
end BKAR.Forest.ActiveTerminalBranchData
