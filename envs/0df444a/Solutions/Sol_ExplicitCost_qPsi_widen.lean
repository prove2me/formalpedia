-- Prove2me | solution 1 for ExplicitCost.qPsi_widen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:53.382501+00:00
-- url     : https://prove2.me/submissions/c96028a2-fccf-44a7-b2d4-76b8108719df

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
    qPsi (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under (widen₂ K g u) = Prod.map (widenC K g) id (qPsi K g asked.under u) := by
  change qPsi (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ _ = _
  rw [kOf_widen, gOf_widen]
  rfl
end ExplicitCost
