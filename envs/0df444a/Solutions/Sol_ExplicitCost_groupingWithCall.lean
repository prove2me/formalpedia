-- Prove2me | solution 1 for ExplicitCost.groupingWithCall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:53.9516+00:00
-- url     : https://prove2.me/submissions/dce4bd07-3451-41c1-806d-8f13bf559594

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Value_End
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingCall
import Theorems.Thm_ExplicitCost_groupingWithCallFrom
import Theorems.Thm_AppRunningTime_groupingSizes
import Theorems.Thm_ExplicitCost_searchCost
import Theorems.Thm_ExplicitCost_searchFinds
import Theorems.Thm_GeneralPieces_groupingSizes
import Theorems.Thm_Value_stValueEqualsZ


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open Sizes
namespace ExplicitCost
theorem _root_.solution : GroupingWithCall :=
  groupingWithCallFrom searchFinds searchCost AppRunningTime.groupingSizes Value.stValueEqualsZ
end ExplicitCost
