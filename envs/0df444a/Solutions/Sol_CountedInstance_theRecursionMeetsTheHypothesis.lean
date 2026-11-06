-- Prove2me | solution 1 for CountedInstance.theRecursionMeetsTheHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:37:39.64942+00:00
-- url     : https://prove2.me/submissions/2a550c49-a5ba-488b-b1de-0a6a1ec1e048

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedInstanceStatement
import Definitions.Def_CountedInstance_Pairs
import Definitions.Def_CountedToPadded_GenLevels
import Definitions.Def_PiecesCounted_Half
import Definitions.Def_PiecesCounted_Assume
import Definitions.Def_CountedRecursion_Main
import Definitions.Def_CountedInstance_Main
import Theorems.Thm_CountedInstance_theRecursionMeetsTheHypothesisFrom
import Theorems.Thm_CliqueLevels_solvesGrowsWithTheConstant
import Theorems.Thm_CountedInstance_thePairsMeetTheClauses
import Theorems.Thm_ExplicitCost_recursionSolves
import Theorems.Thm_GeneralPieces_mayAssume
import Theorems.Thm_PiecesCounted_halfPieces
import Theorems.Thm_PiecesCounted_mayAssume


set_option autoImplicit false
section
section
open CountedInstance
open Groundwork QueryMachines Printed ExplicitCost
namespace CountedInstance
theorem _root_.solution : TheRecursionMeetsTheHypothesis :=
  theRecursionMeetsTheHypothesisFrom PiecesCounted.halfPieces PiecesCounted.mayAssume recursionSolves CliqueLevels.solvesGrowsWithTheConstant thePairsMeetTheClauses
end CountedInstance
