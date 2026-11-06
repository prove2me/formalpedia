-- Prove2me | solution 1 for FixedWidth.runningTimesFromPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:52:33.874128+00:00
-- url     : https://prove2.me/submissions/4ade9345-f3c7-44e3-8020-c9b3dd1e30b4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Numbers
import Definitions.Def_FixedWidthSteps_Small
import Definitions.Def_FixedWidthSteps_Hypothesis
import Definitions.Def_FixedWidthSteps_Choice
import Definitions.Def_FixedWidthSteps_Sentence
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_FrontEnd
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_TwoMachines_Main
import Definitions.Def_RecursionToBound_Main
import Definitions.Def_OccurM_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_FixedWidthSteps_Main
import Theorems.Thm_FixedWidth_countsFromPieces
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_ClausesOccur_countsFromPieces
import Theorems.Thm_FixedWidth_provisoHolds
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_GeneralPieces_PartD_thmRunningTime_d
import Theorems.Thm_GeneralPieces_thmRunningTime_a
import Theorems.Thm_GeneralPieces_thmRunningTime_b
import Theorems.Thm_GeneralPieces_thmRunningTime_d


set_option autoImplicit false
section
section
open FixedWidth
open FixedWidthSteps
namespace FixedWidth
theorem _root_.solution : RunningTimesFromPieces :=
  { a := GeneralPieces.thmRunningTime_a
    b := GeneralPieces.thmRunningTime_b
    c_m := ClausesOccur.countsFromPieces
    c_n := countsFromPieces
    c_proviso := provisoHolds
    d := GeneralPieces.thmRunningTime_d }
end FixedWidth
