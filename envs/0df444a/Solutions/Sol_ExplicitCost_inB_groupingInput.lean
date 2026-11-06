-- Prove2me | solution 1 for ExplicitCost.inB_groupingInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:00.893725+00:00
-- url     : https://prove2.me/submissions/04f416cb-ecc5-49ea-b250-4d89435989e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingNumbers

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)
namespace ExplicitCost
theorem _root_.solution : inB (groupingInput a b K N P B) = B := List.length_replicate
end ExplicitCost
