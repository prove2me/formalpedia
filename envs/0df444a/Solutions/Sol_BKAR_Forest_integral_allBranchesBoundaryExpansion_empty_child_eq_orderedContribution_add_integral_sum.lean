-- Prove2me | solution 1 for BKAR.Forest.integral_allBranchesBoundaryExpansion_empty_child_eq_orderedContribution_add_integral_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:48.920734+00:00
-- url     : https://prove2.me/submissions/d7157be7-4927-4f7a-bcf9-8157f880084a

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_integral_standardInterp_empty_singleton_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
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
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ)
    (hstd :
      IntervalIntegrable
        (fun t : ℝ =>
          mixedPartialList [e.val].reverse ρ
            ((choices (Forest.empty V) e).forest.standardInterp
              ((choices (Forest.empty V) e).forest.paramsOfOrder
                [e.val] [t])))
        MeasureTheory.volume 0 1)
    (hrec :
      IntervalIntegrable
        (fun t : ℝ =>
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
        MeasureTheory.volume 0 1) :
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ +
        ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ) := by
  calc
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (∫ t in 0..(1 : ℝ),
        mixedPartialList [e.val].reverse ρ
          ((choices (Forest.empty V) e).forest.standardInterp
            ((choices (Forest.empty V) e).forest.paramsOfOrder [e.val]
              [t]))) +
        ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ) := by
        simpa using
          integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
            choices (Forest.empty V) e [] [] 1 ρ hstd hrec
    _ =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ +
        ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ) := by
        rw [integral_standardInterp_empty_singleton_eq_orderedContribution]
end BKAR.Forest
