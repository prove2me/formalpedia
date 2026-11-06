-- Prove2me | solution 1 for ExplicitCost.size_groupingInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:16:44.656095+00:00
-- url     : https://prove2.me/submissions/bc6b908e-4f8e-464a-aa48-46220201eca5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_Exits_Runs
import Definitions.Def_Exits_Tested
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingSearch
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size
import Theorems.Thm_Printed_size_unary


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ) :
    size (groupingInput a b K N P B) = size (a, b) + (2 * K + 2 * g + 2 + size (netInput N P B)) := by
  have e : size (groupingInput a b K N P B) = size (a, b) + (size (unary K) + size (unary g) + size (netInput N P B)) := rfl
  rw [e, size_unary, size_unary]
  omega
end ExplicitCost
