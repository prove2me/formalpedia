-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:24:40.582454+00:00
-- url     : https://prove2.me/submissions/4699495c-90e2-421b-b60e-2f5b8359e298

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
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
    (data : TerminalGrowth (Forest.empty V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params emptyParam ts))) :=
  data.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
    emptyParam ρ
end BKAR.Forest.TerminalGrowth
