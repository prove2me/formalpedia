-- Prove2me | solution 1 for ExplicitCost.recursionSolves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:30:44.220552+00:00
-- url     : https://prove2.me/submissions/e14cbd2d-3558-4b03-b0f8-4a0bc716a14c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Base
import Definitions.Def_CountedRecursion_BothNetworks
import Definitions.Def_CountedRecursion_ChildIsGood
import Definitions.Def_CountedRecursion_ProcedureCost
import Definitions.Def_CountedRecursion_SolverStep
import Definitions.Def_CountedRecursion_Meets
import Definitions.Def_CountedRecursion_Expansion
import Definitions.Def_CountedRecursion_Totals
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_CountedRecursion_LabelCrude
import Definitions.Def_CountedRecursion_TotalCount
import Definitions.Def_CountedRecursion_TotalRoom
import Definitions.Def_CountedRecursion_RoomWithin
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_CountedRecursion_PolyAll
import Definitions.Def_CountedRecursion_EndCounted
import Definitions.Def_CountedRecursion_EndPlugged
import Definitions.Def_CountedRecursion_EndSolves
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_Value_End
import Definitions.Def_Tower_TowerRuns
import Definitions.Def_PiecesCounted_Oracle
import Definitions.Def_PiecesCounted_Assume
import Definitions.Def_CountedRecursion_Main
import Theorems.Thm_ExplicitCost_recursionPlugged
import Theorems.Thm_ExplicitCost_readAsRuns
import Theorems.Thm_ExplicitCost_recursionSolvesFrom
import Theorems.Thm_ExplicitCost_recursionWithPoly
import Theorems.Thm_ExplicitCost_roomIsWithinTheBound


set_option autoImplicit false
section
section
open ExplicitCost
open QueryMachines
namespace ExplicitCost
theorem _root_.solution : RecursionSolves := recursionSolvesFrom recursionPlugged roomIsWithinTheBound readAsRuns recursionWithPoly
end ExplicitCost
