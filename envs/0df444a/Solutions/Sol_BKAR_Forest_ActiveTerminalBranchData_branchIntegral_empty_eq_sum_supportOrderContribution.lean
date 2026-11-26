-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:14.107578+00:00
-- url     : https://prove2.me/submissions/c1d836e0-04be-4755-a3a8-f31cc7941db6

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_supportContribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_supportOrderContribution

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
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order => data.supportOrderContribution I order ρ)) := by
  rw [data.branchIntegral_empty_eq_sum_supportContribution ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [data.supportContribution_eq_sum_supportOrderContribution I ρ]
end BKAR.Forest.ActiveTerminalBranchData
