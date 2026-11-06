-- Prove2me | solution 1 for ExplicitCost.qW_widen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:02:14.218722+00:00
-- url     : https://prove2.me/submissions/93bad6f9-7aa7-4e08-a9bb-a20c1cac7797

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_kOf_widen
import Theorems.Thm_ExplicitCost_gOf_widen
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution (u : (X0 NetInput × ℕ) × ℕ) :
    qW (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under.toPaperNetwork (widen₂ K g u) = Prod.map (widenC K g) id (qW K g asked.under.toPaperNetwork u) := by
  change qW (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ _ = _
  rw [kOf_widen, gOf_widen]
  rfl
end ExplicitCost
