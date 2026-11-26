-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:52:17.715233+00:00
-- url     : https://prove2.me/submissions/90d09fbd-166a-4518-9fa7-80742649d274

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_empty_order_eq_zero
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_edgeSetOrders_empty
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
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
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by
  classical
  rw [sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber]
  apply congrArg (fun r => ρ zeroConfig + r)
  let f : ForestIndex V → ℝ :=
    fun I => Finset.sum (edgeSetOrders I.edges)
      (fun order =>
        boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
          I order ρ)
  have hsplit :
      Finset.sum (Finset.univ : Finset (ForestIndex V)) f =
        Finset.sum
            ((Finset.univ : Finset (ForestIndex V)).filter
              (fun I => I.edges ≠ ∅)) f +
          Finset.sum
            ((Finset.univ : Finset (ForestIndex V)).filter
              (fun I => ¬ I.edges ≠ ∅)) f := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (ForestIndex V)))
      (p := fun I => I.edges ≠ ∅) (f := f)]
  rw [hsplit]
  have hzero :
      Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => ¬ I.edges ≠ ∅)) f = 0 := by
    apply Finset.sum_eq_zero
    intro I hI
    rw [Finset.mem_filter] at hI
    have hIempty : I.edges = ∅ := by
      exact Classical.not_not.mp hI.2
    simp [hIempty, edgeSetOrders_empty,
      boundarySupportOrderTreeFiber_empty_order_eq_zero]
  rw [hzero, add_zero]
end BKAR.Forest
