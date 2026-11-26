-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:27.003319+00:00
-- url     : https://prove2.me/submissions/3587fd0a-f0a2-4129-bc06-55babde01129

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_def
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
    {F G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices F order G) :
    ∀ (pref : List (Edge V)) (prefixTs : List ℝ) (top : ℝ)
      (ρ : (Edge V → ℝ) → ℝ),
      order ≠ [] →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
          G.support (pref ++ order) ρ =
        orderedSimplexIntegralAux top order
          (fun ts => mixedPartialList (pref ++ order).reverse ρ
            (G.standardInterp
              (G.paramsOfOrder (pref ++ order) (prefixTs ++ ts))))
  := by
  induction path with
  | nil F =>
      intro pref prefixTs top ρ horder
      exact False.elim (horder rfl)
  | cons he tail ih =>
      rename_i F0 G0 e0 order0
      intro pref prefixTs top ρ _horder
      cases tail with
      | nil Fchild =>
          rw [boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
            choices F0 pref prefixTs top
            (choices F0 ⟨e0, he⟩).forest.support (pref ++ [e0]) ρ
            (by simp)]
          rw [localBoundarySupportOrderContribution_def]
          let e₁ : {e // e ∈ F0.activeEdges} := ⟨e0, he⟩
          have hfilter :
              F0.activeEdges.attach.filter
                  (fun e =>
                    (choices F0 e).forest.support =
                        (choices F0 ⟨e0, he⟩).forest.support ∧
                      pref ++ [e.val] = pref ++ [e₁.val]) =
                {e₁} := by
            ext e
            rw [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · intro h
              exact Subtype.ext (by
                have hcancel : [e.val] = [e₁.val] :=
                  List.append_cancel_left h.2.2
                exact (List.cons.inj hcancel).1)
            · intro h
              rw [h]
              constructor
              · exact Finset.mem_attach _ _
              · constructor
                · rfl
                · rfl
          rw [hfilter, Finset.sum_singleton]
      | cons he₂ tail₂ =>
          rename_i F1 eNext orderTail
          rw [show
              boundarySupportOrderTreeFiber choices F0 pref prefixTs top
                  _ (pref ++ (e0 :: eNext :: orderTail)) ρ =
                ∫ t in 0..top,
                  boundarySupportOrderTreeFiber choices
                    (choices F0 ⟨e0, he⟩).forest (pref ++ [e0])
                    (prefixTs ++ [t]) t _
                    (pref ++ (e0 :: eNext :: orderTail)) ρ by
            exact
              boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
                choices F0 pref prefixTs top _ e0
                (eNext :: orderTail) ρ he (by simp)]
          rw [orderedSimplexIntegralAux_cons]
          apply intervalIntegral.integral_congr
          intro t _ht
          have hchild :=
            ih (pref ++ [e0]) (prefixTs ++ [t]) t ρ (by simp)
          simpa only [List.singleton_append, List.append_assoc] using hchild
end BKAR.Forest
