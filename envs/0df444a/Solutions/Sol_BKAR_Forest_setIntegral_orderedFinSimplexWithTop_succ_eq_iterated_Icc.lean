-- Prove2me | solution 1 for BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:38.216769+00:00
-- url     : https://prove2.me/submissions/3cb9ca51-8edf-465f-828f-f578777905eb

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplexWithTop
import Theorems.Thm_BKAR_Forest_orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail
import Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexWithTop_succ_eq_headTail
import Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc
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
    (top : ℝ) (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : IntegrableOn f (orderedFinSimplexWithTop top (n + 1))) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ t in Set.Icc (0 : ℝ) top,
        ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
  let φ : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let g : ℝ × (Fin n → ℝ) → ℝ :=
    fun z => f (φ.symm z)
  have hsector :
      orderedFinSimplexWithTop top (n + 1) =
        φ ⁻¹' orderedFinSimplexHeadTail top n := by
    exact orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail top n
  have hg : IntegrableOn g (orderedFinSimplexHeadTail top n) := by
    have hcomp :
        IntegrableOn (g ∘ φ) (φ ⁻¹' orderedFinSimplexHeadTail top n) := by
      rw [← hsector]
      refine hf.congr_fun ?_ (measurableSet_orderedFinSimplexWithTop top (n + 1))
      intro ts _hts
      exact congrArg f (φ.left_inv ts).symm
    exact
      ((MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0).integrableOn_comp_preimage
        (MeasurableEquiv.measurableEmbedding φ)
        (f := g)
        (s := orderedFinSimplexHeadTail top n)).mp hcomp
  calc
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts
        = ∫ z in orderedFinSimplexHeadTail top n, g z := by
          exact setIntegral_orderedFinSimplexWithTop_succ_eq_headTail top n f
    _ = ∫ t in Set.Icc (0 : ℝ) top,
          ∫ us in orderedFinSimplexWithTop t n, g (t, us) := by
          exact setIntegral_orderedFinSimplexHeadTail_eq_iterated_Icc top n g hg
    _ = ∫ t in Set.Icc (0 : ℝ) top,
          ∫ us in orderedFinSimplexWithTop t n, f (Fin.cons t us) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro t _ht
          apply setIntegral_congr_fun (measurableSet_orderedFinSimplexWithTop t n)
          intro us _hus
          dsimp [g, φ]
          congr 1
          ext i
          cases i using Fin.cases with
          | zero =>
              simp [Fin.insertNthEquiv]
          | succ i =>
              simp [Fin.insertNthEquiv]
end BKAR.Forest
