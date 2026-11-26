-- Prove2me | solution 1 for BKAR.Forest.localRecursiveBoundaryRemainder_eq_sum_integral_boundarySupportOrderTreeContribution_of_activeEdges_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:04.797241+00:00
-- url     : https://prove2.me/submissions/ec7a2a16-2006-4d50-8c86-35b3c8e2379c

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_def
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_activeEdges_card
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderSum_def
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_def
import Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_eq_sum_integral_child_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder_of_allBranchesAnalytic
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt
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
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      pref.Nodup →
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ →
      localRecursiveBoundaryRemainder choices F pref prefixTs top ρ =
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeContribution choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t ρ)
  | 0, F, pref, prefixTs, top, ρ, hle, _hpref, _hnodup, _hanalytic => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      have hattach : F.activeEdges.attach = ∅ := by
        rw [hF]
        rfl
      rw [localRecursiveBoundaryRemainder_def, hattach]
      simp
  | n + 1, F, pref, prefixTs, top, ρ, hle, hpref, hnodup,
      hanalytic => by
      rw [
        localRecursiveBoundaryRemainder_eq_sum_integral_child_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder_of_allBranchesAnalytic
          choices F pref prefixTs top ρ hpref hnodup hanalytic]
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro t ht
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
        have he_mem : e.val ∈ F.edges := by
          rw [← hpref]
          exact List.mem_toFinset.mpr ha
        exact (choices F e).extension.new_not_mem he_mem
      have hchild_le :
          (choices F e).forest.activeEdges.card ≤ n := by
        have hlt :
            (choices F e).forest.activeEdges.card < F.activeEdges.card :=
          (choices F e).activeEdges_card_lt
        exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
      have hchildAnalytic :
          allBranchesAnalytic choices
            (choices F e).forest.activeEdges.card
            (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
            t ρ :=
        allBranchesAnalytic.child_activeEdges_card choices F e pref prefixTs
          top ρ hanalytic ht
      have hfold :=
        solution
          choices n (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ hchild_le hprefChild hnodupChild
          hchildAnalytic
      calc
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
              (fun I => Finset.sum (edgeSetOrders I.edges)
                (fun order =>
                  localBoundarySupportOrderContribution choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t I order ρ)) +
            localRecursiveBoundaryRemainder choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) =
          Finset.sum (Finset.univ : Finset (ForestIndex V))
              (fun I => Finset.sum (edgeSetOrders I.edges)
                (fun order =>
                  localBoundarySupportOrderContribution choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t I order ρ)) +
            Finset.sum (choices F e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                boundarySupportOrderTreeContribution choices
                  (choices (choices F e).forest e').forest
                  ((pref ++ [e.val]) ++ [e'.val])
                  ((prefixTs ++ [t]) ++ [s]) s ρ) := by
            rw [hfold]
        _ =
          boundarySupportOrderTreeContribution choices
            (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
            t ρ := by
            rw [boundarySupportOrderTreeContribution_def choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t ρ]
            rw [localBoundarySupportOrderSum_def]
end BKAR.Forest
