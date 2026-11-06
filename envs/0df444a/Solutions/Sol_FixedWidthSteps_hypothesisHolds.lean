-- Prove2me | solution 1 for FixedWidthSteps.hypothesisHolds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:10:03.844801+00:00
-- url     : https://prove2.me/submissions/a298b7a3-e0b8-47f0-a3ac-3b288747117e

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
import Theorems.Thm_FixedWidthSteps_chainOfInequalities
import Theorems.Thm_FixedWidthSteps_hypothesisHoldsFrom
import Theorems.Thm_PairsToBound_theRecursionHasLevels


set_option autoImplicit false
section
section
open FixedWidthSteps
namespace FixedWidthSteps
theorem _root_.solution : HypothesisHolds := hypothesisHoldsFrom PairsToBound.theRecursionHasLevels chainOfInequalities
end FixedWidthSteps
