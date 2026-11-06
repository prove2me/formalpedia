-- Prove2me | solution 1 for ExplicitCost.isPsi_widen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:40.888647+00:00
-- url     : https://prove2.me/submissions/28a9f65f-dd72-4ba3-96fe-cee930507801

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_kOf_widen
import Theorems.Thm_ExplicitCost_gOf_widen

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution (u : (X0 NetInput × ℕ) × ℕ) : isPsi (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isPsi K g u := by
  change isPsi (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ = _
  rw [kOf_widen, gOf_widen]
  rfl
end ExplicitCost
