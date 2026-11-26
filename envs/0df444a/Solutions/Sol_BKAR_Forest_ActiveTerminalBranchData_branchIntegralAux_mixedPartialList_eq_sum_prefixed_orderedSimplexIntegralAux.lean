-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:52.444375+00:00
-- url     : https://prove2.me/submissions/9d590053-a785-4d2d-ae4e-e92cb2c50261

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Prefixed
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_growth_branchIntegralAux
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_mixedPartialList_eq_orderedSimplexIntegralAux_paramsOfOrder_append


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
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top (F.paramsOfOrder pref prefixTs)
        (mixedPartialList pref.reverse ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (data.growth e).order
          (fun ts => mixedPartialList (pref ++ (data.growth e).order).reverse ρ
            ((data.growth e).terminal.standardInterp
              ((data.growth e).terminal.paramsOfOrder
                (pref ++ (data.growth e).order) (prefixTs ++ ts))))) := by
  rw [data.branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (data.growth e).branchIntegralAux_mixedPartialList_eq_orderedSimplexIntegralAux_paramsOfOrder_append
    pref prefixTs hpref hprefixTs top ρ
end BKAR.Forest.ActiveTerminalBranchData
