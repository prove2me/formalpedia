-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_singletonBranchIntegralAux_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:14.34738+00:00
-- url     : https://prove2.me/submissions/88762277-99df-4128-beba-e900cda810cd

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        (ActiveBranchData.singleton extensions).branchIntegralAux b u
          (mixedPartialList es ρ) := by
  rw [F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
    es u ρ b hbound hρ hint extensions]
  rw [ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    extensions es b u ρ hterm]
end BKAR.Forest
