-- Prove2me | solution 1 for BKAR.BKARContDiff.allBranchesBoundaryExpansion_continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:26.812673+00:00
-- url     : https://prove2.me/submissions/d5b21bc7-887d-4cc4-b4e2-39a6a89f0469

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_BKARContDiff_continuous
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_succ
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
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      {X : Type*} [TopologicalSpace X]
      {tsPath : X → List ℝ} {topPath : X → ℝ},
      BKAR.ListPathContinuous pref.length tsPath →
      Continuous topPath →
      Continuous
        (fun x : X =>
          Forest.allBranchesBoundaryExpansion choices n F pref
            (tsPath x) (topPath x) ρ)
  | 0, F, pref, X, _inst, tsPath, _topPath, hts, _htop => by
      have hparam :
          Continuous (fun x : X => F.paramsOfOrder pref (tsPath x)) :=
        Forest.paramsOfOrder_continuous_of_listPathContinuous F pref hts
      have hpath :
          Continuous
            (fun x : X =>
              F.standardInterp (F.paramsOfOrder pref (tsPath x))) :=
        F.standardInterp_continuous_comp hparam
      exact (hρ.mixedPartialList pref.reverse).continuous.comp hpath
  | n + 1, F, pref, X, _inst, tsPath, topPath, hts, htop => by
      rw [show
          (fun x : X =>
            Forest.allBranchesBoundaryExpansion choices (n + 1) F pref
              (tsPath x) (topPath x) ρ) =
          fun x : X =>
            BKAR.mixedPartialList pref.reverse ρ
              (F.standardInterp (F.paramsOfOrder pref (tsPath x))) +
              Finset.sum F.activeEdges.attach
                (fun e => ∫ t in 0..topPath x,
                  Forest.allBranchesBoundaryExpansion choices n
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t ρ) by
        funext x
        rw [Forest.allBranchesBoundaryExpansion_succ]]
      apply Continuous.add
      · have hparam :
            Continuous (fun x : X => F.paramsOfOrder pref (tsPath x)) :=
          Forest.paramsOfOrder_continuous_of_listPathContinuous F pref hts
        have hpath :
            Continuous
              (fun x : X =>
                F.standardInterp (F.paramsOfOrder pref (tsPath x))) :=
          F.standardInterp_continuous_comp hparam
        exact (hρ.mixedPartialList pref.reverse).continuous.comp hpath
      · apply continuous_finsetSum
        intro e _he
        have htsChild :
            BKAR.ListPathContinuous (pref ++ [e.val]).length
              (fun p : X × ℝ => tsPath p.1 ++ [p.2]) := by
          simpa using
            BKAR.ListPathContinuous.append_singleton
              (BKAR.ListPathContinuous.comp hts continuous_fst)
              continuous_snd
        have hchild :
            Continuous
              (fun p : X × ℝ =>
                Forest.allBranchesBoundaryExpansion choices n
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath p.1 ++ [p.2]) p.2 ρ) :=
          solution hρ choices n
            (choices F e).forest (pref ++ [e.val])
            htsChild continuous_snd
        have huncurry :
            Continuous
              (Function.uncurry
                (fun x : X => fun t : ℝ =>
                  Forest.allBranchesBoundaryExpansion choices n
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t ρ)) := by
          simpa [Function.uncurry] using! hchild
        exact
          intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (μ := MeasureTheory.volume) (a₀ := 0)
            (f :=
              fun x : X => fun t : ℝ =>
                Forest.allBranchesBoundaryExpansion choices n
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath x ++ [t]) t ρ)
            huncurry htop
end BKAR.BKARContDiff
