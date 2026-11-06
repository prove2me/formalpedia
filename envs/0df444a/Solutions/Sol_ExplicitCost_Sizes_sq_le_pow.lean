-- Prove2me | solution 1 for ExplicitCost.Sizes.sq_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:17:57.748338+00:00
-- url     : https://prove2.me/submissions/1be9a2bb-4b99-4edd-9e3e-40a58a224933

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Cost

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open ExplicitCost.Sizes
namespace ExplicitCost.Sizes
theorem _root_.solution {X : ℕ} (hX : 2 ≤ X) : 256 * (X * X) ≤ X ^ 10 :=
  calc 256 * (X * X) = 2 ^ 8 * (X * X) := by norm_num
    _ ≤ X ^ 8 * (X * X) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hX 8)
    _ = X ^ 10 := by ring
end ExplicitCost.Sizes
