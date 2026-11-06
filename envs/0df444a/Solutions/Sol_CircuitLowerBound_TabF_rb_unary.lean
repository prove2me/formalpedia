-- Prove2me | solution 1 for CircuitLowerBound.TabF.rb_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:33:30.905464+00:00
-- url     : https://prove2.me/submissions/4e483674-10ae-4e1d-b6a5-7fe088e0ce03

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_TabF_size_le_self
import Theorems.Thm_CircuitLowerBound_Sched_tab_polyT
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution {e : α → MCode} (he : PolyT e) : Unary fun x => rb (e x) :=
  Unary.of_le (Unary.of_length (tab_polyT he)) (PolyT.size' (PolyT.length (tab_polyT he))) fun _ => size_le_self _
end CircuitLowerBound.TabF
