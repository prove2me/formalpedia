-- Prove2me | solution 1 for BKAR.Forest.pairMeasurableEquivOfPair_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:08:53.288227+00:00
-- url     : https://prove2.me/submissions/01a0cb9c-1016-4fe8-989e-988e1775d0bf

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
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
    (u : F.EdgeParam → ℝ) :
    F.pairMeasurableEquivOfPair hedges hne u =
      F.pairCoordOfOrder e₁ e₂ u := by
  have he₁ : e₁ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_self e₁ {e₂}
  have he₂ : e₂ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
  ext
  · simp only [pairMeasurableEquivOfPair, pairCoordOfOrder,
      MeasurableEquiv.trans_apply]
    rw [F.paramValue_of_mem u he₁]
    change ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 0 =
      u ⟨e₁, he₁⟩
    change ((Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 0 =
      u ⟨e₁, he₁⟩
    simp [edgeParamFinTwoEquivOfPair]
  · simp only [pairMeasurableEquivOfPair, pairCoordOfOrder,
      MeasurableEquiv.trans_apply]
    rw [F.paramValue_of_mem u he₂]
    change ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 1 =
      u ⟨e₂, he₂⟩
    change ((Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
        (F.edgeParamFinTwoEquivOfPair hedges hne)).symm u) 1 =
      u ⟨e₂, he₂⟩
    simp [edgeParamFinTwoEquivOfPair]
end BKAR.Forest
