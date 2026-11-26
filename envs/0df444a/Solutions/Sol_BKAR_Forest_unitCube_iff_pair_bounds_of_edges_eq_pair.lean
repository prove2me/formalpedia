-- Prove2me | solution 1 for BKAR.Forest.unitCube_iff_pair_bounds_of_edges_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:19.848201+00:00
-- url     : https://prove2.me/submissions/1afc7995-bbf3-497e-b765-f01525618ec2

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
import Theorems.Thm_BKAR_Forest_mem_unitCube_iff
import Theorems.Thm_BKAR_Forest_paramValue_mem_Icc
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
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V)))
    (u : F.EdgeParam → ℝ) :
    u ∈ F.unitCube ↔
      0 ≤ F.paramValue u e₁ ∧ F.paramValue u e₁ ≤ 1 ∧
        0 ≤ F.paramValue u e₂ ∧ F.paramValue u e₂ ≤ 1 := by
  have he₁ : e₁ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_self e₁ {e₂}
  have he₂ : e₂ ∈ F.edges := by
    rw [hedges]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
  constructor
  · intro hu
    have hcube := (F.mem_unitCube_iff u).mp hu
    exact ⟨(F.paramValue_mem_Icc u hcube e₁).1,
      (F.paramValue_mem_Icc u hcube e₁).2,
      (F.paramValue_mem_Icc u hcube e₂).1,
      (F.paramValue_mem_Icc u hcube e₂).2⟩
  · intro hbounds
    rw [F.mem_unitCube_iff]
    intro p
    rcases F.edgeParam_eq_left_or_right_of_edges_eq_pair hedges p with hp | hp
    · have hp_eq : p = ⟨e₁, he₁⟩ := Subtype.ext hp
      rw [hp_eq]
      have hpair :
          0 ≤ F.paramValue u e₁ ∧ F.paramValue u e₁ ≤ 1 :=
        ⟨hbounds.1, hbounds.2.1⟩
      simpa [F.paramValue_of_mem u he₁] using hpair
    · have hp_eq : p = ⟨e₂, he₂⟩ := Subtype.ext hp
      rw [hp_eq]
      have hpair :
          0 ≤ F.paramValue u e₂ ∧ F.paramValue u e₂ ≤ 1 :=
        ⟨hbounds.2.2.1, hbounds.2.2.2⟩
      simpa [F.paramValue_of_mem u he₂] using hpair
end BKAR.Forest
