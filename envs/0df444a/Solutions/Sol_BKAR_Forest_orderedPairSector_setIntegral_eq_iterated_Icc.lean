-- Prove2me | solution 1 for BKAR.Forest.orderedPairSector_setIntegral_eq_iterated_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:47.372181+00:00
-- url     : https://prove2.me/submissions/860eda41-9bb0-487f-8d71-617fdfa40dad

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_measurableSet_orderedPairSector
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
theorem _root_.solution
    (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f orderedPairSector) :
    ∫ z in orderedPairSector, f z =
      ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) x, f (x, y) := by
  let rect : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)
  have hrect_inter : rect ∩ orderedPairSector = orderedPairSector := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨⟨⟨hz.1, hz.2.1⟩, trivial⟩, hz⟩
  have hind :
      IntegrableOn (orderedPairSector.indicator f) rect
        (volume : Measure (ℝ × ℝ)) :=
    (hf.integrable_indicator measurableSet_orderedPairSector).integrableOn
  calc
    ∫ z in orderedPairSector, f z
        = ∫ z in rect, orderedPairSector.indicator f z := by
          rw [setIntegral_indicator measurableSet_orderedPairSector]
          rw [hrect_inter]
    _ = ∫ x in Set.Icc (0 : ℝ) 1,
          ∫ y in (Set.univ : Set ℝ), orderedPairSector.indicator f (x, y) := by
          exact setIntegral_prod (orderedPairSector.indicator f) hind
    _ = ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) x, f (x, y) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro x hx
          have hfiber :
              (fun y : ℝ => orderedPairSector.indicator f (x, y)) =
                (Set.Icc (0 : ℝ) x).indicator (fun y : ℝ => f (x, y)) := by
            funext y
            have hmem : (x, y) ∈ orderedPairSector ↔ y ∈ Set.Icc (0 : ℝ) x := by
              constructor
              · intro hy
                exact ⟨hy.2.2.1, hy.2.2.2.2⟩
              · intro hy
                exact ⟨hx.1, hx.2, hy.1, hy.2.trans hx.2, hy.2⟩
            by_cases hy : y ∈ Set.Icc (0 : ℝ) x
            · have hsector : (x, y) ∈ orderedPairSector := hmem.mpr hy
              simp [Set.indicator_of_mem hsector, Set.indicator_of_mem hy]
            · have hsector : (x, y) ∉ orderedPairSector := by
                intro h
                exact hy (hmem.mp h)
              simp [Set.indicator_of_notMem hsector, Set.indicator_of_notMem hy]
          change (∫ y in (Set.univ : Set ℝ),
              orderedPairSector.indicator f (x, y)) =
            ∫ y in Set.Icc (0 : ℝ) x, f (x, y)
          rw [setIntegral_univ, hfiber, integral_indicator measurableSet_Icc]
end BKAR.Forest
