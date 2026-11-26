-- Prove2me | solution 1 for BKAR.BKARContDiff.allBranchesAnalytic_child_recursive_sum_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:47.524282+00:00
-- url     : https://prove2.me/submissions/9c2f4584-3292-4ec6-a1fc-d52f231e92c2

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_BKARContDiff_allBranchesBoundaryExpansion_continuous_comp
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
import Theorems.Thm_BKAR_ListPathContinuous_append_singleton
import Theorems.Thm_BKAR_ListPathContinuous_const
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
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ) (top : ℝ)
    (hprefixTs : prefixTs.length = pref.length) :
    IntervalIntegrable
      (fun t : ℝ =>
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            Forest.allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ))
      MeasureTheory.volume 0 top := by
  apply Continuous.intervalIntegrable
  apply continuous_finsetSum
  intro e' _he'
  have htsBase :
      BKAR.ListPathContinuous pref.length
        (fun _ : ℝ × ℝ => prefixTs) := by
    rw [← hprefixTs]
    exact BKAR.ListPathContinuous.const prefixTs
  have htsChild :
      BKAR.ListPathContinuous (pref ++ [e.val]).length
        (fun p : ℝ × ℝ => prefixTs ++ [p.1]) := by
    simpa using
      BKAR.ListPathContinuous.append_singleton
        htsBase continuous_fst
  have htsGrandchild :
      BKAR.ListPathContinuous
        (((pref ++ [e.val]) ++ [e'.val]).length)
        (fun p : ℝ × ℝ => (prefixTs ++ [p.1]) ++ [p.2]) := by
    simpa using
      BKAR.ListPathContinuous.append_singleton
        htsChild continuous_snd
  have hchild :
      Continuous
        (fun p : ℝ × ℝ =>
          Forest.allBranchesBoundaryExpansion choices
            (choices (choices F e).forest e').forest.activeEdges.card
            (choices (choices F e).forest e').forest
            ((pref ++ [e.val]) ++ [e'.val])
            ((prefixTs ++ [p.1]) ++ [p.2]) p.2 ρ) :=
    hρ.allBranchesBoundaryExpansion_continuous_comp choices
      (choices (choices F e).forest e').forest.activeEdges.card
      (choices (choices F e).forest e').forest
      ((pref ++ [e.val]) ++ [e'.val])
      htsGrandchild continuous_snd
  have huncurry :
      Continuous
        (Function.uncurry
          (fun t s : ℝ =>
            Forest.allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
    simpa [Function.uncurry] using! hchild
  exact
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0)
      (f :=
        fun t s : ℝ =>
          Forest.allBranchesBoundaryExpansion choices
            (choices (choices F e).forest e').forest.activeEdges.card
            (choices (choices F e).forest e').forest
            ((pref ++ [e.val]) ++ [e'.val])
            ((prefixTs ++ [t]) ++ [s]) s ρ)
      huncurry continuous_id
end BKAR.BKARContDiff
