-- Prove2me | solution 1 for BKAR.BKARContDiff.boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:46.655787+00:00
-- url     : https://prove2.me/submissions/37ea32ce-e0ce-4afc-87cc-2c5d919eae6e

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Theorems.Thm_BKAR_BKARContDiff_localBoundarySupportOrderContribution_continuous_comp
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_def
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
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
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      {X : Type*} [TopologicalSpace X]
      {tsPath : X → List ℝ} {topPath : X → ℝ},
      BKAR.ListPathContinuous pref.length tsPath →
      Continuous topPath →
      (I : ForestIndex V) → (order : List (Edge V)) →
      order.length = pref.length + k →
      Continuous
        (fun x : X =>
          Forest.boundarySupportOrderTreeFiber choices F pref (tsPath x)
            (topPath x) I order ρ)
  | 0, F, pref, X, _inst, tsPath, topPath, hts, _htop, I, order, hlen => by
      have hfiber_zero :
          (fun x : X =>
            Forest.boundarySupportOrderTreeFiber choices F pref (tsPath x)
              (topPath x) I order ρ) = fun _ : X => 0 := by
        funext x
        exact
          Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
            choices F.activeEdges.card F pref (tsPath x) (topPath x)
            I order ρ le_rfl (by
              rw [hlen]
              simp)
      rw [hfiber_zero]
      exact continuous_const
  | k + 1, F, pref, X, _inst, tsPath, topPath, hts, htop, I, order, hlen => by
      have hfiber_def :
          (fun x : X =>
            Forest.boundarySupportOrderTreeFiber choices F pref (tsPath x)
              (topPath x) I order ρ) =
          fun x : X =>
            Forest.localBoundarySupportOrderContribution choices F pref
                (tsPath x) (topPath x) I order ρ +
              Finset.sum F.activeEdges.attach
                (fun e => ∫ t in 0..topPath x,
                  Forest.boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t I order ρ) := by
        funext x
        rw [Forest.boundarySupportOrderTreeFiber_def]
      rw [hfiber_def]
      apply Continuous.add
      · exact
          hρ.localBoundarySupportOrderContribution_continuous_comp
            choices F pref hts htop I order
      · apply continuous_finsetSum
        intro e _he
        have htsChild :
            BKAR.ListPathContinuous (pref ++ [e.val]).length
              (fun p : X × ℝ => tsPath p.1 ++ [p.2]) := by
          simpa using
            BKAR.ListPathContinuous.append_singleton
              (BKAR.ListPathContinuous.comp hts continuous_fst)
              continuous_snd
        have hlenChild :
            order.length = (pref ++ [e.val]).length + k := by
          rw [hlen]
          simp [Nat.add_assoc, Nat.add_comm]
        have hchild :
            Continuous
              (fun p : X × ℝ =>
                Forest.boundarySupportOrderTreeFiber choices
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath p.1 ++ [p.2]) p.2 I order ρ) :=
          solution
            hρ choices k (choices F e).forest (pref ++ [e.val])
            htsChild continuous_snd I order hlenChild
        have huncurry :
            Continuous
              (Function.uncurry
                (fun x : X => fun t : ℝ =>
                  Forest.boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t I order ρ)) := by
          simpa [Function.uncurry] using! hchild
        exact
          intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (μ := MeasureTheory.volume) (a₀ := 0)
            (f :=
              fun x : X => fun t : ℝ =>
                Forest.boundarySupportOrderTreeFiber choices
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath x ++ [t]) t I order ρ)
            huncurry htop
end BKAR.BKARContDiff
