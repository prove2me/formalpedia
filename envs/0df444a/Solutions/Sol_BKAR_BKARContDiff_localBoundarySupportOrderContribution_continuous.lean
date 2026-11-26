-- Prove2me | solution 1 for BKAR.BKARContDiff.localBoundarySupportOrderContribution_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:59.921804+00:00
-- url     : https://prove2.me/submissions/d4ad8b31-1fda-4108-8590-7cae459da2fb

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous_comp
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_EdgeExtension_paramsOfOrder_append_singleton_continuous
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_standardInterp_continuous_comp
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_intervalIntegral_continuous_primitive_of_continuous
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
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (I : ForestIndex V) (order : List (Edge V)) :
    Continuous
      (fun top : ℝ =>
        Forest.localBoundarySupportOrderContribution choices F pref prefixTs
          top I order ρ) := by
  classical
  change
    Continuous
      (fun top : ℝ =>
        Finset.sum
          (F.activeEdges.attach.filter
            (fun e =>
              (choices F e).forest.support = I ∧
                pref ++ [e.val] = order))
          (fun e =>
            orderedSimplexIntegralAux top [e.val]
              (fun ts =>
                BKAR.mixedPartialList order.reverse ρ
                  ((choices F e).forest.standardInterp
                    ((choices F e).forest.paramsOfOrder order
                      (prefixTs ++ ts))))))
  apply continuous_finsetSum
  intro e he
  have horder : pref ++ [e.val] = order :=
    (Finset.mem_filter.mp he).2.2
  have hparam :
      Continuous
        (fun t : ℝ =>
          (choices F e).forest.paramsOfOrder order (prefixTs ++ [t])) := by
    rw [← horder]
    exact
      (choices F e).extension.paramsOfOrder_append_singleton_continuous
        pref prefixTs hpref hprefixTs
  have hpath :
      Continuous
        (fun t : ℝ =>
          (choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder order (prefixTs ++ [t]))) :=
    (choices F e).forest.standardInterp_continuous_comp hparam
  have hintegrand :
      Continuous
        (fun t : ℝ =>
          BKAR.mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order
                (prefixTs ++ [t])))) :=
    hρ.mixedPartialList_continuous_comp order.reverse hpath
  simpa using
    BKAR.intervalIntegral_continuous_primitive_of_continuous
      hintegrand 0
end BKAR.BKARContDiff
