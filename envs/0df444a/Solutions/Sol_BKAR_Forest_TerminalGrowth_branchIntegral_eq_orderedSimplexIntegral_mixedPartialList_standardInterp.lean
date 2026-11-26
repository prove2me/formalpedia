-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:25.373799+00:00
-- url     : https://prove2.me/submissions/b8247e5d-fdef-4ecc-b2dc-94e7a8e725e6

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
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
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params u ts))) :=
  data.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    1 u ρ
end BKAR.Forest.TerminalGrowth
