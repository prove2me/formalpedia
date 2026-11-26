-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_not_mem_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:07.188323+00:00
-- url     : https://prove2.me/submissions/ebbb150e-94a8-4373-8cae-16905b1748c3

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_def
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_def
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
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      pref.Nodup →
      order ∉ edgeSetOrders I.edges →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  | 0, F, pref, prefixTs, top, I, order, ρ, hle, _hpref, _hnodup, _horder => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      exact boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top I order ρ hF
  | n + 1, F, pref, prefixTs, top, I, order, ρ, hle, hpref, hnodup, horder => by
      rw [boundarySupportOrderTreeFiber_def]
      have hlocal :
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ = 0 := by
        rw [localBoundarySupportOrderContribution_def]
        rw [Finset.filter_eq_empty_iff.mpr]
        · exact Finset.sum_empty
        · intro e _ he
          apply horder
          rw [← he.2]
          exact
            activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
              (choices F e) hpref hnodup he.1
      rw [hlocal, zero_add]
      apply Finset.sum_eq_zero
      intro e _
      have hchild_le :
          (choices F e).forest.activeEdges.card ≤ n := by
        have hlt :
            (choices F e).forest.activeEdges.card <
              F.activeEdges.card :=
          (choices F e).activeEdges_card_lt
        exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
      have hprefChild :
          (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
        rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
        simp
      have hnodupChild : (pref ++ [e.val]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnodup, List.nodup_singleton e.val, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst b
        subst a
        have ha_edges : e.val ∈ F.edges := by
          rw [← hpref]
          exact List.mem_toFinset.mpr ha
        exact (choices F e).extension.new_not_mem ha_edges
      have hzero :
          ∀ t : ℝ,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ = 0 := by
        intro t
        exact
          solution
            choices n (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t I order ρ hchild_le hprefChild
            hnodupChild horder
      rw [show
          (fun t : ℝ =>
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ) = fun _ => 0 by
        funext t
        exact hzero t]
      simp
end BKAR.Forest
