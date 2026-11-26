-- Prove2me | solution 1 for BKAR.Forest.measurableSet_orderedSimplexParams_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:51.648795+00:00
-- url     : https://prove2.me/submissions/e836400b-e9a4-4d75-b077-09ae8d079464

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_measurableSet_orderedSimplexParams_map
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
omit [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (n : ℕ) :
    MeasurableSet
      {ts : Fin n → ℝ | OrderedSimplexParams 1 (List.ofFn ts)} := by
  let fs : List ((Fin n → ℝ) → ℝ) :=
    List.ofFn fun i : Fin n => fun ts : Fin n → ℝ => ts i
  have hfs : ∀ f ∈ fs, Measurable f := by
    simp [fs, measurable_pi_apply]
  have hmeas :
      MeasurableSet
        {ts : Fin n → ℝ |
          OrderedSimplexParams ((fun _ : Fin n → ℝ => (1 : ℝ)) ts)
            (fs.map fun f => f ts)} :=
    measurableSet_orderedSimplexParams_map fs measurable_const hfs
  convert hmeas using 1
  ext ts
  simp [fs, List.map_ofFn, Function.comp_def]
end BKAR.Forest
