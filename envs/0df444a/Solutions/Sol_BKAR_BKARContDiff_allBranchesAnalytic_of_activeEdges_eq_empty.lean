-- Prove2me | solution 1 for BKAR.BKARContDiff.allBranchesAnalytic_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:37:21.802649+00:00
-- url     : https://prove2.me/submissions/17473056-cda4-4582-9880-2317997be4b0

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_differentiableAt
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_zero


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
      F.activeEdges = ∅ →
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) →
      Forest.allBranchesAnalytic choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, _hF, _hbound => by
      exact Forest.allBranchesAnalytic_zero choices F pref prefixTs top ρ
  | n + 1, F, pref, prefixTs, top, hF, hbound => by
      rw [Forest.allBranchesAnalytic]
      refine ⟨hbound, ?_, ?_, ?_, ?_, ?_⟩
      · intro t _ht
        exact hρ.mixedPartialList_differentiableAt pref.reverse
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)
      · intro e he
        have he_empty : e ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact he
        exact False.elim (Finset.notMem_empty e he_empty)
      · intro e
        have he_empty : e.val ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact e.property
        exact False.elim (Finset.notMem_empty e.val he_empty)
      · intro e
        have he_empty : e.val ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact e.property
        exact False.elim (Finset.notMem_empty e.val he_empty)
      · intro e
        have he_empty : e.val ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact e.property
        exact False.elim (Finset.notMem_empty e.val he_empty)
end BKAR.BKARContDiff
