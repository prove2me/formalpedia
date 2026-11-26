-- Prove2me | solution 1 for BKAR.BKARContDiff.allBranchesAnalytic_smooth_obligations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:46.97586+00:00
-- url     : https://prove2.me/submissions/fd427012-0e76-437c-b844-728eed894858

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_differentiableAt
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_interpWithFill_intervalIntegrable
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    (∀ t ∈ Set.uIcc 0 top,
      DifferentiableAt ℝ (BKAR.mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) ∧
    (∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ =>
          BKAR.mixedPartialList (e :: pref.reverse) ρ
            (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
        MeasureTheory.volume 0 top) ∧
    (∀ e : {e // e ∈ F.activeEdges},
      IntervalIntegrable
        (fun t : ℝ =>
          BKAR.mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
        MeasureTheory.volume 0 top) := by
  constructor
  · intro t _ht
    exact hρ.mixedPartialList_differentiableAt pref.reverse
      (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)
  constructor
  · intro e _he
    exact hρ.mixedPartialList_interpWithFill_intervalIntegrable
      (e :: pref.reverse) F (F.paramsOfOrder pref prefixTs) 0 top
  · intro e
    exact
      hρ.mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
        (pref ++ [e.val]).reverse (choices F e).extension
        pref prefixTs hpref hprefixTs 0 top
end BKAR.BKARContDiff
