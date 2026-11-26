-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_interpWithFill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:41.82647+00:00
-- url     : https://prove2.me/submissions/a6c8d178-cc99-488d-8a64-22459fa2e31a

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegral u ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.interpWithFill (data.growth.params u ts) b)) :=
  data.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
    1 u ρ b
end BKAR.Forest.TerminalGrowth
