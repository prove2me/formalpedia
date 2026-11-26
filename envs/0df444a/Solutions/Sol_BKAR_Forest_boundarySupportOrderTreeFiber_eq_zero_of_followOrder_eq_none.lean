-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:02.308651+00:00
-- url     : https://prove2.me/submissions/0a70caea-3268-40be-8e88-a05492950b7b

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_next_not_mem_activeEdges
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
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
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
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) :
    ∀ (order : List (Edge V)) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (ρ : (Edge V → ℝ) → ℝ),
      followOrder? choices F order = none →
      boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ order) ρ = 0
  | [], _F, _pref, _prefixTs, _top, _I, _ρ, hnone => by
      simp [followOrder?] at hnone
  | e :: tail, F, pref, prefixTs, top, I, ρ, hnone => by
      by_cases he : e ∈ F.activeEdges
      · simp [followOrder?, he] at hnone
        by_cases htail : tail = []
        · subst tail
          simp [followOrder?] at hnone
        · rw [show
            boundarySupportOrderTreeFiber choices F pref prefixTs top I
                (pref ++ (e :: tail)) ρ =
              ∫ t in 0..top,
                boundarySupportOrderTreeFiber choices
                  (choices F ⟨e, he⟩).forest (pref ++ [e])
                  (prefixTs ++ [t]) t I
                  (pref ++ (e :: tail)) ρ by
          exact
            boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
              choices F pref prefixTs top I e tail ρ he htail]
          have hzero :
              (fun t : ℝ =>
                boundarySupportOrderTreeFiber choices
                  (choices F ⟨e, he⟩).forest (pref ++ [e])
                  (prefixTs ++ [t]) t I
                  (pref ++ (e :: tail)) ρ) = fun _ => 0 := by
            funext t
            have hchild :=
              solution
                choices tail (choices F ⟨e, he⟩).forest
                (pref ++ [e]) (prefixTs ++ [t]) t I ρ hnone
            rw [← @List.singleton_append (Edge V) e tail, ← List.append_assoc]
            exact hchild
          rw [hzero]
          simp
      · exact
          boundarySupportOrderTreeFiber_eq_zero_of_next_not_mem_activeEdges
            choices F pref prefixTs top I e tail ρ he
end BKAR.Forest
