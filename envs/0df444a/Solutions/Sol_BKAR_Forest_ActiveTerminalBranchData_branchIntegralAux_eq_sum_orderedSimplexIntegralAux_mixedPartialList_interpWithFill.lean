-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:35.819372+00:00
-- url     : https://prove2.me/submissions/5df1c079-5a7a-48b9-86e6-ac4f9f6d2c30

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchData_terminal_activeEdges_eq_empty
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: (data.tail e).order)
          (fun ts => mixedPartialList (e.val :: (data.tail e).order).reverse ρ
            ((data.tail e).terminal.interpWithFill
              ((data.growth e).growth.params u ts) b))) :=
  data.branchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    data.branchData_terminal_activeEdges_eq_empty top u ρ b
end BKAR.Forest.ActiveTerminalBranchData
