-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_prefixed_orderedSimplexIntegralAux_sub_sum_localFirstTailRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:13.279391+00:00
-- url     : https://prove2.me/submissions/360b8493-314b-4a35-802c-71f90ba1b27e

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData F)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam,
      t ≤ F.paramsOfOrder pref prefixTs e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: pref.reverse) ρ
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
        MeasureTheory.volume 0 b) :
    mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) b) =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => orderedSimplexIntegralAux b (data.growth e).order
            (fun ts =>
              mixedPartialList (pref ++ (data.growth e).order).reverse ρ
                ((data.growth e).terminal.standardInterp
                  ((data.growth e).terminal.paramsOfOrder
                    (pref ++ (data.growth e).order) (prefixTs ++ ts))))) -
          Finset.sum F.activeEdges.attach
            (fun e => data.localFirstTailRemainder e b
              (F.paramsOfOrder pref prefixTs) pref.reverse ρ) := by
  rw [data.mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
    pref.reverse (F.paramsOfOrder pref prefixTs) ρ b hbound hρ hint]
  rw [data.branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux
    pref prefixTs hpref hprefixTs b ρ]
end BKAR.Forest.ActiveTerminalBranchData
