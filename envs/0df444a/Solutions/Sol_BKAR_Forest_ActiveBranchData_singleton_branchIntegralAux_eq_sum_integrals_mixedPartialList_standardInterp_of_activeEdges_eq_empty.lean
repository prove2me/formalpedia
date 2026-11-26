-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:09.864582+00:00
-- url     : https://prove2.me/submissions/a2dd90c0-d383-4770-8d4d-55496dcf1642

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_Forest_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) := by
  rw [singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    extensions es top u ρ hterm]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr
  intro t _
  change mixedPartialList (e.val :: es) ρ
      ((extensions e).forest.interpWithFill
        ((extensions e).extension.extendParam u t) t) =
    mixedPartialList (e.val :: es) ρ
      ((extensions e).forest.standardInterp
        ((extensions e).extension.extendParam u t))
  rw [(extensions e).forest.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    ((extensions e).extension.extendParam u t) t (hterm e)]
end BKAR.Forest.ActiveBranchData
