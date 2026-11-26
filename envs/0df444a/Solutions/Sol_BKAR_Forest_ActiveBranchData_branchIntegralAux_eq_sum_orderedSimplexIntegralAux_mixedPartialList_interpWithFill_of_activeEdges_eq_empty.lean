-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:22:24.647641+00:00
-- url     : https://prove2.me/submissions/5fcd0ce1-d64a-4036-9f59-9d43012c54be

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution
    (data : ActiveBranchData F)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (data.terminal e).activeEdges = ∅)
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).interpWithFill
              ((data.growth e).params u ts) b))) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  rw [OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top (e.val :: data.order e)
    (fun ts =>
      data.growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
        hterm e u ρ ts b)
end BKAR.Forest.ActiveBranchData
