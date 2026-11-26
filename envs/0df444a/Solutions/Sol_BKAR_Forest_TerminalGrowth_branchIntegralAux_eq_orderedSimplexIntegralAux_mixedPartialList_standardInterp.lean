-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:57.752796+00:00
-- url     : https://prove2.me/submissions/96f75b21-6671-488a-a548-0e4ce0cc370e

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def_standardInterp
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
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params u ts))) := by
  rw [branchIntegralAux, OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top data.order
    (fun ts => data.growth.branchIntegrand_def_standardInterp u ρ ts)
end BKAR.Forest.TerminalGrowth
