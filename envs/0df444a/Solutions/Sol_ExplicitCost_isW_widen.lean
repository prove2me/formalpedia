-- Prove2me | solution 1 for ExplicitCost.isW_widen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:23:09.037193+00:00
-- url     : https://prove2.me/submissions/0defba62-cdb2-4999-9e7d-26e177720a7e

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
theorem _root_.solution (u : (X0 NetInput × ℕ) × ℕ) : isW (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isW g u := by
  change isW (gOf (widen K g u.1.1)) _ = _
  rw [gOf_widen]
  rfl
end ExplicitCost
