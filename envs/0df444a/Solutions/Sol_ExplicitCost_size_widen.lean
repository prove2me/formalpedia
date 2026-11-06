-- Prove2me | solution 1 for ExplicitCost.size_widen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:17:44.786891+00:00
-- url     : https://prove2.me/submissions/d5bf25ab-6c00-413e-a622-27d3a368c683

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_size_widenC

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution (u : X0 NetInput) : size (widen K g u) = size u + (2 * K + 2 * g + 2) := by
  change size (widenC K g u.1.1) + size u.1.2 + size u.2 = size u.1.1 + size u.1.2 + size u.2 + _
  rw [size_widenC]
  omega
end ExplicitCost
