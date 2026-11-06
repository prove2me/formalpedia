-- Prove2me | solution 1 for ExplicitCost.Sizes.add_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:24.360231+00:00
-- url     : https://prove2.me/submissions/99e759b5-ae0d-4c48-aace-b5377650948d

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

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open ExplicitCost.Sizes
namespace ExplicitCost.Sizes
theorem _root_.solution {Z n u v w : ℕ} (hZ : 2 ≤ Z) (hu : u ≤ Z ^ n) (hv : v ≤ Z ^ n) (hw : w ≤ Z ^ n) : u + v + w ≤ Z ^ (n + 2) := by
  have h : 2 * 2 * Z ^ n ≤ Z * Z * Z ^ n := Nat.mul_le_mul_right _ (Nat.mul_le_mul hZ hZ)
  have e : Z ^ (n + 2) = Z * Z * Z ^ n := by ring
  rw [e]
  omega
end ExplicitCost.Sizes
