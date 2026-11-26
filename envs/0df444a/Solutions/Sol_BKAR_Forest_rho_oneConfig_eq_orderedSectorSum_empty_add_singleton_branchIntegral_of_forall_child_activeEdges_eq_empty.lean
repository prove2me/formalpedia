-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:51.221059+00:00
-- url     : https://prove2.me/submissions/a3a8fce1-f450-4531-919f-055da8de5aa6

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_growth_branchIntegralAux
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_empty_edges
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_paramsOfOrder_empty
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (ActiveTerminalBranchData.singleton
          (fun e => choices (Forest.empty V) e) hterm).branchIntegral
            emptyParam ρ := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  apply congrArg
    (fun r => (Forest.empty V).orderedSectorSum ρ + r)
  rw [ActiveTerminalBranchData.branchIntegral_eq_branchIntegralAux_one]
  rw [ActiveTerminalBranchData.branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  simpa [ActiveTerminalBranchData.singleton, ActiveTerminalBranchData.growth,
    paramsOfOrder_empty] using
    integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
      choices (Forest.empty V) e [] [] (by simp [Forest.empty_edges]) rfl
      1 ρ (hterm e)
end BKAR.Forest
