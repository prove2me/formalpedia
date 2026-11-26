-- Prove2me | solution 1 for BKAR.BKARContDiff.allBranchesAnalytic_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:39.542568+00:00
-- url     : https://prove2.me/submissions/58ef246f-96db-40d2-a017-e790e41766b1

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_parameterBound_child
import Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_smooth_obligations
import Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_child_recursive_sum_intervalIntegrable
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_zero
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
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      pref.toFinset = F.edges →
      prefixTs.length = pref.length →
      0 ≤ top →
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) →
      Forest.allBranchesAnalytic choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, _hpref, _hprefixTs, _htop, _hbound => by
      exact Forest.allBranchesAnalytic_zero choices F pref prefixTs top ρ
  | n + 1, F, pref, prefixTs, top, hpref, hprefixTs, htop, hbound => by
      rw [Forest.allBranchesAnalytic]
      have hsmooth :=
        hρ.allBranchesAnalytic_smooth_obligations choices F pref prefixTs
          top hpref hprefixTs
      refine ⟨hbound, hsmooth.1, hsmooth.2.1, hsmooth.2.2, ?_, ?_⟩
      · intro e
        exact
          hρ.allBranchesAnalytic_child_recursive_sum_intervalIntegrable
            choices F e pref prefixTs top hprefixTs
      · intro e t ht
        let child := (choices F e).forest
        have hprefChild : (pref ++ [e.val]).toFinset = child.edges := by
          rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
          simp
        have hprefixTsChild :
            (prefixTs ++ [t]).length = (pref ++ [e.val]).length := by
          simp [hprefixTs]
        have htIcc : t ∈ Set.Icc 0 top := by
          simpa [Set.uIcc_of_le htop] using ht
        have hboundChild :
            ∀ s ∈ Set.uIcc 0 t,
              ∀ e' : child.EdgeParam,
                s ≤ child.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ [t]) e' :=
          allBranchesAnalytic_parameterBound_child choices F pref prefixTs
            top hpref hprefixTs htop hbound e ht
        exact
          solution hρ choices n child
            (pref ++ [e.val]) (prefixTs ++ [t]) t
            hprefChild hprefixTsChild htIcc.1 hboundChild
end BKAR.BKARContDiff
