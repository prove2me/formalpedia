-- Prove2me | solution 1 for FixedWidth.countsFromPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:46:14.252195+00:00
-- url     : https://prove2.me/submissions/a794feec-5ff5-4547-99d7-1bc7e23fe2de

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
import Theorems.Thm_FixedWidthSteps_hypothesisHolds
import Theorems.Thm_FixedWidthSteps_everyChoiceCounts
import Theorems.Thm_FixedWidthSteps_rateOfThePairs
import Theorems.Thm_FixedWidthSteps_sentenceFromTheSteps
import Theorems.Thm_PairsToBound_exhaustiveMachineExists
import Theorems.Thm_PairsToBound_frontEndAndTestExist
import Theorems.Thm_RecursionToBound_thmVariablesAWithNumberBetween
import Theorems.Thm_TwoMachines_everyTwoMachinesCanBeChosenBetween


set_option autoImplicit false
section
section
open FixedWidth
open FixedWidthSteps
namespace FixedWidth
theorem _root_.solution : CountsFromPieces :=
  sentenceFromTheSteps RecursionToBound.thmVariablesAWithNumberBetween hypothesisHolds rateOfThePairs TwoMachines.everyTwoMachinesCanBeChosenBetween PairsToBound.frontEndAndTestExist PairsToBound.exhaustiveMachineExists
    everyChoiceCounts
end FixedWidth
