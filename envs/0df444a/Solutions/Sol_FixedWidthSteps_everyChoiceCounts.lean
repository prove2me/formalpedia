-- Prove2me | solution 1 for FixedWidthSteps.everyChoiceCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:18.888884+00:00
-- url     : https://prove2.me/submissions/be556c0c-3c50-4f1a-b62c-f048c133d3cc

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
import Theorems.Thm_FixedWidthSteps_conditionsHoldEventually
import Theorems.Thm_FixedWidthSteps_everyChoiceCountsFrom
import Theorems.Thm_FixedWidthSteps_smallCasesAreWithinTheBound
import Theorems.Thm_MainTheoremForms_thmVariablesAInParticular
import Theorems.Thm_PairsToBound_widthOr3Stmt
import Theorems.Thm_VariableBound_VariablesA_thmVariablesAInParticular


set_option autoImplicit false
section
section
open FixedWidthSteps
namespace FixedWidthSteps
theorem _root_.solution : EveryChoiceCounts :=
  everyChoiceCountsFrom MainTheoremForms.thmVariablesAInParticular conditionsHoldEventually smallCasesAreWithinTheBound PairsToBound.widthOr3Stmt
end FixedWidthSteps
