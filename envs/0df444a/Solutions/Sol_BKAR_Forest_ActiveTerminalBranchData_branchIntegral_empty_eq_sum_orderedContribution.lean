-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:46.845091+00:00
-- url     : https://prove2.me/submissions/fe91df08-7d95-4e82-8647-cdf3870b9f4d

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_growth_branchIntegralAux
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_branchIntegralAux_one
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
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (data.growth e).terminal.orderedContribution
          (e.val :: (data.tail e).order) ρ) := by
  rw [branchIntegral_eq_branchIntegralAux_one]
  rw [branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (data.growth e).branchIntegral_emptyStart_eq_orderedContribution ρ
end BKAR.Forest.ActiveTerminalBranchData
