-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_growthOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:47.916022+00:00
-- url     : https://prove2.me/submissions/9dda097e-ddd2-4654-9d6e-e168920f1905

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_eq
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_orderedContribution

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
          (data.growthOrder e) ρ) := by
  rw [data.branchIntegral_empty_eq_sum_orderedContribution ρ]
  apply Finset.sum_congr rfl
  intro e _
  rw [data.growthOrder_eq e]
end BKAR.Forest.ActiveTerminalBranchData
