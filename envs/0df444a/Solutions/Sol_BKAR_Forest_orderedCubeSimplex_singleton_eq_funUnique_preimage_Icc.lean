-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:12.541797+00:00
-- url     : https://prove2.me/submissions/3db9788f-458e-466f-ba87-ebb1fdf395b5

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_mem_orderedCubeSimplex_iff
import Theorems.Thm_BKAR_Forest_mem_unitCube_iff
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
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    F.orderedCubeSimplex [e] =
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance) ⁻¹'
        Set.Icc (0 : ℝ) 1 := by
  let : Unique F.EdgeParam := F.uniqueEdgeParamOfEdgesSingleton hedges
  ext u
  have he : e ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_singleton_self e
  let p₀ : F.EdgeParam := ⟨e, he⟩
  have hunit :
      u ∈ F.unitCube ↔ (0 : ℝ) ≤ u p₀ ∧ u p₀ ≤ 1 := by
    rw [F.mem_unitCube_iff]
    constructor
    · intro hu
      exact hu p₀
    · intro hu p
      rw [Subsingleton.elim p p₀]
      exact hu
  have hparam : F.paramValue u e = u p₀ := by
    exact F.paramValue_of_mem u he
  have hdefault : (default : F.EdgeParam) = p₀ :=
    Subsingleton.elim default p₀
  rw [mem_orderedCubeSimplex_iff]
  simp [hunit, hparam, OrderedSimplexParams, hdefault]
end BKAR.Forest
