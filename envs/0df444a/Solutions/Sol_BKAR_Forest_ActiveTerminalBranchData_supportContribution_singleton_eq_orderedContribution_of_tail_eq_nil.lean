-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_orderedContribution_of_tail_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:16.535564+00:00
-- url     : https://prove2.me/submissions/0352daf3-c839-4792-ae34-d24b03b52f9e

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_singleton_eq_sum_first_eq_and_tail_nil
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_eq
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
    (a : Edge V) (htail : (data.tail (emptyActiveEdge a)).order = [])
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ =
      (data.growth (emptyActiveEdge a)).terminal.orderedContribution [a] ρ := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => e.val = a ∧ (data.tail e).order = []) =
        {emptyActiveEdge a} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      apply Subtype.ext
      rw [emptyActiveEdge_val]
      exact h.2.1
    · intro h
      rw [h]
      exact ⟨Finset.mem_attach _ _, rfl, htail⟩
  rw [data.supportContribution_singleton_eq_sum_first_eq_and_tail_nil a ρ]
  rw [hfilter, Finset.sum_singleton]
  rw [data.growthOrder_eq (emptyActiveEdge a), htail, emptyActiveEdge_val]
end BKAR.Forest.ActiveTerminalBranchData
