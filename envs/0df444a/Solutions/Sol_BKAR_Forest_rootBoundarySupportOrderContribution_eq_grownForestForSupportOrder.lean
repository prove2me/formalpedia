-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:36.256124+00:00
-- url     : https://prove2.me/submissions/57396d0c-9d2a-4b13-bf9a-d11c858c5d5f

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_BKAR_ForestIndex_canonicalOrder_val
import Theorems.Thm_P2M_BKAR_Forest_followOrder__grownForestForSupportOrder_bd48bf0ce40b
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_support
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeSetOrders
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
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


attribute [local simp] BKAR.ForestIndex.canonicalOrder_val

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order.val =
      (grownForestForSupportOrder choices I order).orderedContribution
        order.val ρ := by
  cases horderList : order.val with
  | nil =>
      have hI : I.edges = ∅ := by
        have hset : ([] : List (Edge V)).toFinset = I.edges := by
          simpa [horderList] using
            toFinset_eq_of_mem_edgeSetOrders order.property
        simpa using hset.symm
      have hgrown :
          grownForestForSupportOrder choices I order = Forest.empty V := by
        have hfollow :=
          followOrder?_grownForestForSupportOrder choices I order
        simp [followOrder?, horderList] at hfollow
        exact hfollow.symm
      rw [hgrown]
      exact rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
        choices ρ I hI
  | cons e tail =>
      have hsupport :
          (grownForestForSupportOrder choices I order).support = I :=
        grownForestForSupportOrder_support choices I order
      have hroot :=
        rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
          choices
          (followOrder?_grownForestForSupportOrder choices I order)
          ρ
          (by
            rw [horderList]
            simp)
      simpa [horderList, hsupport] using hroot
end BKAR.Forest
