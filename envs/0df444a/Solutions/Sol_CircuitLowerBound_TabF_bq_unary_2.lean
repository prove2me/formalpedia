-- Prove2me | solution 2 for CircuitLowerBound.TabF.bq_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:45:38.880886+00:00
-- url     : https://prove2.me/submissions/d7c6f7e5-52d6-4fb5-bf9e-e61042d2add4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_Sched_bt_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_Unary_add


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
variable {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hk : Unary fun x => kb (e x)) (hl : Unary fun x => lam (e x)) (hL : Unary L) (hP : PolyT P)
include he hk hl hL
omit hk
namespace CircuitLowerBound.TabF
theorem _root_.solution : Unary fun x => bq (e x) (L x) := (bt_unary he hL).add hl
end CircuitLowerBound.TabF
