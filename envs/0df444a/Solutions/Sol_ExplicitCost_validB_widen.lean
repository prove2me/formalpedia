-- Prove2me | solution 1 for ExplicitCost.validB_widen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:24:09.592981+00:00
-- url     : https://prove2.me/submissions/250daa51-7537-4d72-821c-acd34d73e738

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
theorem _root_.solution (u : X0 NetInput) : validB (kOf (widen K g u)) (gOf (widen K g u)) askedData.under.toPaperNetwork (widen K g u) = validB K g asked.under.toPaperNetwork u := by
  rw [kOf_widen, gOf_widen]
  rfl
end ExplicitCost
