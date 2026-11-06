-- Prove2me | solution 1 for ExplicitCost.groupingExplicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:09:17.980042+00:00
-- url     : https://prove2.me/submissions/2f971717-a9b2-45b9-8a6d-c2fa867f6087

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_Achievable
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingLemma
import Theorems.Thm_ExplicitCost_groupingExplicitFrom
import Theorems.Thm_AppRunningTime_groupingSizes
import Theorems.Thm_ExplicitCost_entryCostExplicit
import Theorems.Thm_ExplicitCost_groupingWithCall
import Theorems.Thm_ExplicitCost_labelLengthIsL
import Theorems.Thm_GeneralPieces_groupingSizes
import Theorems.Thm_Printed_stMono
import Theorems.Thm_QueryMachines_stMono
import Theorems.Thm_QueryMachines_stSlowDown
import Theorems.Thm_QueryMachines_stSubstWithin


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes
namespace ExplicitCost
theorem _root_.solution : GroupingExplicit :=
  groupingExplicitFrom groupingWithCall labelLengthIsL entryCostExplicit AppRunningTime.groupingSizes stMono stSlowDown stSubstWithin
end ExplicitCost
