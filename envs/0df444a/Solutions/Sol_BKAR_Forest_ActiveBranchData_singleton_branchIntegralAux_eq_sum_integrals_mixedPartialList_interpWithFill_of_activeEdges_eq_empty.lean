-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:22:20.62331+00:00
-- url     : https://prove2.me/submissions/2cbc8239-2c18-4112-aea8-a162f3c68a68

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegralAux_eq_sum_integrals_partialDeriv_interpWithFill_of_activeEdges_eq_empty

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
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by
  rw [singleton_branchIntegralAux_eq_sum_integrals_partialDeriv_interpWithFill_of_activeEdges_eq_empty
    extensions top u (mixedPartialList es ρ) hterm]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr
  intro t _
  rfl
end BKAR.Forest.ActiveBranchData
