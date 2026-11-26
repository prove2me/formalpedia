-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:12.177882+00:00
-- url     : https://prove2.me/submissions/6c4563a4-6dbb-49a3-8b09-fafbd0c5a102

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_pairCoordOfOrder_pairMeasurableEquivOfPair_symm
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_of_ne
import Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_self
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
attribute [local simp] BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
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
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (z : ℝ × ℝ) :
    F.paramsOfOrder [e₁, e₂] [z.1, z.2] =
      (F.pairMeasurableEquivOfPair hedges hne).symm z := by
  have he₁ : e₁ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_self e₁ {e₂}
  have he₂ : e₂ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
  have hcoord := F.pairCoordOfOrder_pairMeasurableEquivOfPair_symm hedges hne z
  have hleft :
      ((F.pairMeasurableEquivOfPair hedges hne).symm z) ⟨e₁, he₁⟩ = z.1 := by
    have hfst := congrArg Prod.fst hcoord
    simpa [pairCoordOfOrder, F.paramValue_of_mem _ he₁] using hfst
  have hright :
      ((F.pairMeasurableEquivOfPair hedges hne).symm z) ⟨e₂, he₂⟩ = z.2 := by
    have hsnd := congrArg Prod.snd hcoord
    simpa [pairCoordOfOrder, F.paramValue_of_mem _ he₂] using hsnd
  funext p
  rcases F.edgeParam_eq_left_or_right_of_edges_eq_pair hedges p with hp | hp
  · have hp_eq : p = ⟨e₁, he₁⟩ := Subtype.ext hp
    rw [hp_eq]
    rw [F.paramsOfOrder_cons_self e₁ [e₂] z.1 [z.2] he₁]
    exact hleft.symm
  · have hp_eq : p = ⟨e₂, he₂⟩ := Subtype.ext hp
    rw [hp_eq]
    rw [F.paramsOfOrder_cons_of_ne [e₂] z.1 [z.2] he₂ hne.symm]
    simpa using hright.symm
end BKAR.Forest
