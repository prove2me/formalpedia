-- Prove2me | solution 1 for CircuitLowerBound.TabF.lam_clipE_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:32:55.481574+00:00
-- url     : https://prove2.me/submissions/3816aa9a-6c7f-4d57-a663-c3ffb74e8b4b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_Sched_lam_polyT
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : Unary L) : Unary fun x => lam (clipE (e x) (L x)) :=
  Unary.of_le hL (PolyT.min' (lam_polyT he) hL.poly) fun _ => Nat.min_le_right _ _
end CircuitLowerBound.TabF
