-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:26.05658+00:00
-- url     : https://prove2.me/submissions/637773d4-abe4-4206-99fd-95c1a7ab498e

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.interpWithFill (data.growth.params u ts) b)) := by
  rw [branchIntegralAux, OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top data.order
    (fun ts =>
      data.growth.branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
        u ρ ts b data.terminal_activeEdges_eq_empty)
end BKAR.Forest.TerminalGrowth
