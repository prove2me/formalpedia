-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:22:32.947906+00:00
-- url     : https://prove2.me/submissions/f45b66e2-372b-471b-b0b5-ed0093914880

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_branchIntegrand_eq_mixedPartialList_standardInterp
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
    (data : ActiveBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).standardInterp
              ((data.growth e).params u ts)))) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  rw [OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top (e.val :: data.order e)
    (fun ts =>
      data.growth_branchIntegrand_eq_mixedPartialList_standardInterp e u ρ ts)
end BKAR.Forest.ActiveBranchData
