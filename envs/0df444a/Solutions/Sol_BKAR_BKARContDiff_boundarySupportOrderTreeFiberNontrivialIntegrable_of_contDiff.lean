-- Prove2me | solution 1 for BKAR.BKARContDiff.boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:56.742494+00:00
-- url     : https://prove2.me/submissions/d6093ccc-a5cc-4724-895d-089ab61125b4

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Theorems.Thm_BKAR_BKARContDiff_boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiberNontrivialIntegrable_zero
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
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      prefixTs.length = pref.length →
      Forest.boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, _hprefixTs => by
      exact
        Forest.boundarySupportOrderTreeFiberNontrivialIntegrable_zero
          choices F pref prefixTs top ρ
  | n + 1, F, pref, prefixTs, top, hprefixTs => by
      constructor
      · intro e x _hx hlen_gt _hI
        let childPref := pref ++ [e.val]
        let k := x.2.length - childPref.length
        have htsBase :
            BKAR.ListPathContinuous pref.length
              (fun _ : ℝ => prefixTs) := by
          rw [← hprefixTs]
          exact BKAR.ListPathContinuous.const prefixTs
        have htsChild :
            BKAR.ListPathContinuous childPref.length
              (fun t : ℝ => prefixTs ++ [t]) := by
          simpa [childPref] using
            BKAR.ListPathContinuous.append_singleton
              htsBase continuous_id
        have hlen :
            x.2.length = childPref.length + k := by
          dsimp [k, childPref]
          omega
        exact
          (boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
            hρ choices k (choices F e).forest childPref htsChild
            continuous_id x.1 x.2 hlen).intervalIntegrable 0 top
      · intro e t _ht
        exact
          solution
            hρ choices n (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
            t (by simp [hprefixTs])
end BKAR.BKARContDiff
