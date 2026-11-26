-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.branchIntegral_eq_sum_orderedSimplexIntegral_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:10.131506+00:00
-- url     : https://prove2.me/submissions/38088323-4afe-45ee-88a3-57ef60163dcf

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


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
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegral (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).standardInterp
              ((data.growth e).params u ts)))) :=
  data.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    1 u ρ
end BKAR.Forest.ActiveBranchData
