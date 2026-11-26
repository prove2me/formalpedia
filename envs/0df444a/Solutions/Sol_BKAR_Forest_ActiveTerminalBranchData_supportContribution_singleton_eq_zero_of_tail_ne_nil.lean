-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_zero_of_tail_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:35.481797+00:00
-- url     : https://prove2.me/submissions/0fd5d939-bfd4-4496-8c30-6046c9a31a9e

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_singleton_eq_sum_first_eq_and_tail_nil
import Theorems.Thm_BKAR_ForestIndex_ext
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
    (a : Edge V) (htail : (data.tail (emptyActiveEdge a)).order ≠ [])
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ = 0 := by
  rw [data.supportContribution_singleton_eq_sum_first_eq_and_tail_nil a ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    have heq : e = emptyActiveEdge a := by
      apply Subtype.ext
      rw [emptyActiveEdge_val]
      exact h.1
    exact htail (by
      rw [← h.2]
      rw [heq])
end BKAR.Forest.ActiveTerminalBranchData
