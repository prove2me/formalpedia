-- Prove2me | solution 1 for ClausesOccur.runningTimesFromPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:53.324239+00:00
-- url     : https://prove2.me/submissions/8ab4988b-6520-43ab-9cd4-60ad6f11771d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_OccurM_Main
import Theorems.Thm_ClausesOccur_countsFromPieces
import Theorems.Thm_AppRunningTime_thmRunningTime
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_GeneralPieces_thmRunningTime


set_option autoImplicit false
section
section
open ClausesOccur
open Turing MainTheoremForms
namespace ClausesOccur
theorem _root_.solution : RunningTimesFromPieces :=
  ⟨AppRunningTime.thmRunningTime.a, AppRunningTime.thmRunningTime.b, countsFromPieces, AppRunningTime.thmRunningTime.c_n, AppRunningTime.thmRunningTime.d⟩
end ClausesOccur
