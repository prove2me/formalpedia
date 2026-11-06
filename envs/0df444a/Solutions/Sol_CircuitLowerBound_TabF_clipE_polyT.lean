-- Prove2me | solution 1 for CircuitLowerBound.TabF.clipE_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:33:45.06714+00:00
-- url     : https://prove2.me/submissions/de6c2be4-58b1-42a4-9937-5c1bdf2f6971

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_Sched_kb_polyT
import Theorems.Thm_CircuitLowerBound_Sched_lam_polyT
import Theorems.Thm_CircuitLowerBound_Sched_tab_polyT
import Theorems.Thm_Groundwork_PolyT_prodMk
attribute [local fun_prop] Groundwork.PolyT.prodMk



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : PolyT L) : PolyT fun x => clipE (e x) (L x) :=
  (PolyT.min' (kb_polyT he) hL).prodMk ((PolyT.min' (lam_polyT he) hL).prodMk (tab_polyT he))
end CircuitLowerBound.TabF
