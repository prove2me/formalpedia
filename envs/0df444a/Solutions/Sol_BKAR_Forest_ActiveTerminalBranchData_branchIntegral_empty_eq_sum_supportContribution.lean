-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:04.011585+00:00
-- url     : https://prove2.me/submissions/bc98bbb7-fa30-4499-8ef3-f8898f16baa8

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_def
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_growthOrderContribution


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
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => data.supportContribution I ρ) := by
  classical
  rw [data.branchIntegral_empty_eq_sum_growthOrderContribution ρ]
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach,
        (data.growth e).support ∈
          (Finset.univ : Finset (ForestIndex V)) := by
    intro e _
    exact Finset.mem_univ (data.growth e).support
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach)
      (t := (Finset.univ : Finset (ForestIndex V)))
      (g := fun e => (data.growth e).support)
      hmap
      (fun e => (data.growth e).terminal.orderedContribution
        (data.growthOrder e) ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro I _
  rw [data.supportContribution_def I ρ]
end BKAR.Forest.ActiveTerminalBranchData
