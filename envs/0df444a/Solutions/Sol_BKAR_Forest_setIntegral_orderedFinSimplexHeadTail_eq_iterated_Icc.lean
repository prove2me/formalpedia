-- Prove2me | solution 1 for BKAR.Forest.setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:15.694978+00:00
-- url     : https://prove2.me/submissions/b86729b2-89a4-4985-96a5-43a87d18846e

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplexWithTop
import Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplexHeadTail
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
    (top : ℝ) (n : ℕ) (f : ℝ × (Fin n → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexHeadTail top n)) :
    ∫ z in orderedFinSimplexHeadTail top n, f z =
      ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (t, us) := by
  let rect : Set (ℝ × (Fin n → ℝ)) :=
    Set.Icc (0 : ℝ) top ×ˢ (Set.univ : Set (Fin n → ℝ))
  have hrect_inter : rect ∩ orderedFinSimplexHeadTail top n =
      orderedFinSimplexHeadTail top n := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨⟨hz.1, trivial⟩, hz⟩
  have hsector : MeasurableSet (orderedFinSimplexHeadTail top n) :=
    measurableSet_orderedFinSimplexHeadTail top n
  have hind :
      IntegrableOn ((orderedFinSimplexHeadTail top n).indicator f) rect
        (volume : Measure (ℝ × (Fin n → ℝ))) :=
    (hf.integrable_indicator hsector).integrableOn
  calc
    ∫ z in orderedFinSimplexHeadTail top n, f z
        = ∫ z in rect, (orderedFinSimplexHeadTail top n).indicator f z := by
          rw [setIntegral_indicator hsector]
          rw [hrect_inter]
    _ = ∫ t in Set.Icc (0 : ℝ) top,
          ∫ us in (Set.univ : Set (Fin n → ℝ)),
            (orderedFinSimplexHeadTail top n).indicator f (t, us) := by
          exact setIntegral_prod
            ((orderedFinSimplexHeadTail top n).indicator f) hind
    _ = ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (t, us) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro t ht
          have hfiber :
              (fun us : Fin n → ℝ =>
                  (orderedFinSimplexHeadTail top n).indicator f (t, us)) =
                (orderedFinSimplexWithTop t n).indicator
                  (fun us : Fin n → ℝ => f (t, us)) := by
            funext us
            have hmem :
                (t, us) ∈ orderedFinSimplexHeadTail top n ↔
                  us ∈ orderedFinSimplexWithTop t n := by
              constructor
              · intro hus
                exact hus.2
              · intro hus
                exact ⟨ht, hus⟩
            by_cases hus : us ∈ orderedFinSimplexWithTop t n
            · have hhead : (t, us) ∈ orderedFinSimplexHeadTail top n :=
                hmem.mpr hus
              simp [Set.indicator_of_mem hhead, Set.indicator_of_mem hus]
            · have hhead : (t, us) ∉ orderedFinSimplexHeadTail top n := by
                intro h
                exact hus (hmem.mp h)
              simp [Set.indicator_of_notMem hhead, Set.indicator_of_notMem hus]
          change (∫ us in (Set.univ : Set (Fin n → ℝ)),
              (orderedFinSimplexHeadTail top n).indicator f (t, us)) =
            ∫ us in orderedFinSimplexWithTop t n, f (t, us)
          rw [setIntegral_univ, hfiber,
            integral_indicator (measurableSet_orderedFinSimplexWithTop t n)]
end BKAR.Forest
