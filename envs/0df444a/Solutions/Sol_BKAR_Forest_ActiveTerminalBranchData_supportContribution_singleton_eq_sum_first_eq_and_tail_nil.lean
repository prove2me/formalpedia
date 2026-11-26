-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_sum_first_eq_and_tail_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:11.2129+00:00
-- url     : https://prove2.me/submissions/1e6e7d9f-8405-4d17-934e-07eac2711089

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_singleton_iff_emptyStart
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_def
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
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => e.val = a ∧ (data.tail e).order = []))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = ForestIndex.singleton a) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e => e.val = a ∧ (data.tail e).order = []) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr_right
      (fun _ => data.growth_support_eq_singleton_iff_emptyStart e a)
  rw [data.supportContribution_def (ForestIndex.singleton a) ρ, hfilter]
end BKAR.Forest.ActiveTerminalBranchData
