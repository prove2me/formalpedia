-- Prove2me | solution 1 for BKAR.BKARContDiff.localBoundarySupportOrderContribution_continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:21.173267+00:00
-- url     : https://prove2.me/submissions/b04a4f4d-6af1-4fcc-909d-e035cfe890da

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Theorems.Thm_BKAR_BKARContDiff_continuous
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_paramsOfOrder_continuous_of_listPathContinuous
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_standardInterp_continuous_comp
import Theorems.Thm_BKAR_ListPathContinuous_append_singleton
import Theorems.Thm_BKAR_ListPathContinuous_comp
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
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V))
    {X : Type*} [TopologicalSpace X]
    {tsPath : X → List ℝ} {topPath : X → ℝ}
    (hts : BKAR.ListPathContinuous pref.length tsPath)
    (htop : Continuous topPath)
    (I : ForestIndex V) (order : List (Edge V)) :
    Continuous
      (fun x : X =>
        Forest.localBoundarySupportOrderContribution choices F pref
          (tsPath x) (topPath x) I order ρ) := by
  classical
  change
    Continuous
      (fun x : X =>
        Finset.sum
          (F.activeEdges.attach.filter
            (fun e =>
              (choices F e).forest.support = I ∧
                pref ++ [e.val] = order))
          (fun e =>
            orderedSimplexIntegralAux (topPath x) [e.val]
              (fun ts =>
                BKAR.mixedPartialList order.reverse ρ
                  ((choices F e).forest.standardInterp
                    ((choices F e).forest.paramsOfOrder order
                      (tsPath x ++ ts))))))
  apply continuous_finsetSum
  intro e _he
  have htsProd :
      BKAR.ListPathContinuous (pref.length + 1)
        (fun p : X × ℝ => tsPath p.1 ++ [p.2]) :=
    BKAR.ListPathContinuous.append_singleton
      (BKAR.ListPathContinuous.comp hts continuous_fst)
      continuous_snd
  have hparam :
      Continuous
        (fun p : X × ℝ =>
          (choices F e).forest.paramsOfOrder order (tsPath p.1 ++ [p.2])) :=
    Forest.paramsOfOrder_continuous_of_listPathContinuous
      (choices F e).forest order htsProd
  have hpath :
      Continuous
        (fun p : X × ℝ =>
          (choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder order
              (tsPath p.1 ++ [p.2]))) :=
    (choices F e).forest.standardInterp_continuous_comp hparam
  have hintegrand :
      Continuous
        (Function.uncurry
          (fun x : X => fun t : ℝ =>
            BKAR.mixedPartialList order.reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder order
                  (tsPath x ++ [t]))))) := by
    change
      Continuous
        (fun p : X × ℝ =>
          BKAR.mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order
                (tsPath p.1 ++ [p.2]))))
    exact (hρ.mixedPartialList order.reverse).continuous.comp hpath
  simpa using
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0)
      (f :=
        fun x : X => fun t : ℝ =>
          BKAR.mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order
                (tsPath x ++ [t]))))
      hintegrand htop
end BKAR.BKARContDiff
