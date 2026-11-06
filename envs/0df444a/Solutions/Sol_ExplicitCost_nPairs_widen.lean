-- Prove2me | solution 1 for ExplicitCost.nPairs_widen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:23:35.915101+00:00
-- url     : https://prove2.me/submissions/f3fc57e9-11ce-458d-b940-2069c533c100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_gOf_widen

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution (v : X0 NetInput × ℕ) : nPairs (gOf (widen₁ K g v).1) (widen₁ K g v) = nPairs g v := by
  change nPairs (gOf (widen K g v.1)) _ = _
  rw [gOf_widen]
  rfl
end ExplicitCost
