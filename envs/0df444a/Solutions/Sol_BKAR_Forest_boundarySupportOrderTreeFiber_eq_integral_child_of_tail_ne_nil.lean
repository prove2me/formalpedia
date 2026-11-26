-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:06.229716+00:00
-- url     : https://prove2.me/submissions/dbafb59f-385b-4a74-9c23-fd35732cadee

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_def
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_eq_zero_of_length_ne
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
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V)
    (e₀ : Edge V) (tail : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (he₀ : e₀ ∈ F.activeEdges)
    (htail : tail ≠ []) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ e₀ :: tail) ρ =
      ∫ t in 0..top,
        boundarySupportOrderTreeFiber choices
          (choices F ⟨e₀, he₀⟩).forest (pref ++ [e₀])
          (prefixTs ++ [t]) t I (pref ++ e₀ :: tail) ρ := by
  rw [boundarySupportOrderTreeFiber_def]
  have hlocal :
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I (pref ++ e₀ :: tail) ρ = 0 := by
    apply
      localBoundarySupportOrderContribution_eq_zero_of_length_ne
        choices F pref prefixTs top I (pref ++ e₀ :: tail) ρ
    intro hlen
    have htailLength : tail.length = 0 := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    exact htail (List.length_eq_zero_iff.mp htailLength)
  rw [hlocal, zero_add]
  rw [Finset.sum_eq_single_of_mem ⟨e₀, he₀⟩ (Finset.mem_attach _ _)]
  intro e _ hne
  have hnotPrefix :
      ¬ ∃ rest : List (Edge V),
        (pref ++ [e.val]) ++ rest = pref ++ e₀ :: tail := by
    intro hbad
    rcases hbad with ⟨rest, hrest⟩
    have hcancel : e.val :: rest = e₀ :: tail := by
      have hsame :
          pref ++ (e.val :: rest) = pref ++ (e₀ :: tail) := by
        rw [← @List.singleton_append (Edge V) e.val rest, ← List.append_assoc]
        exact hrest
      exact List.append_cancel_left hsame
    have hfirst : e.val = e₀ := by
      exact (List.cons.inj hcancel).1
    apply hne
    exact Subtype.ext hfirst
  have hzero :
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t I (pref ++ e₀ :: tail) ρ) = fun _ => 0 := by
    funext t
    exact
      boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
        choices (choices F e).forest.activeEdges.card (choices F e).forest
        (pref ++ [e.val]) (prefixTs ++ [t]) t I (pref ++ e₀ :: tail)
        ρ le_rfl hnotPrefix
  rw [hzero]
  simp
end BKAR.Forest
