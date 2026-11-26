-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegral_empty_eq_sum_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:40.168014+00:00
-- url     : https://prove2.me/submissions/95037a1c-4ac4-4100-9e1b-f9404f040db4

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_branchIntegral_empty_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_growth_branchIntegralAux
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_branchIntegralAux_one


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (extensions :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        ActiveExtension (Forest.empty V) e.val)
    (hterm :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        (extensions e).forest.activeEdges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (extensions e).forest.orderedContribution [e.val] ρ) := by
  rw [branchIntegral_eq_branchIntegralAux_one]
  rw [branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  change ((extensions e).singletonGrowth.branchIntegral emptyParam ρ) =
    (extensions e).forest.orderedContribution [e.val] ρ
  exact (extensions e).singletonGrowth_branchIntegral_empty_eq_orderedContribution ρ
end BKAR.Forest.ActiveTerminalBranchData
