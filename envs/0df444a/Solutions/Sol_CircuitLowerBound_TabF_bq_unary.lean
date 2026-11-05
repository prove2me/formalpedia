-- Prove2me | solution 1 for CircuitLowerBound.TabF.bq_unary
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:33:15.594191+00:00
-- url     : https://prove2.me/submissions/85c912b6-a1e7-4245-8ea5-3312088e7155

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_Sched_kb_polyT
import Theorems.Thm_CircuitLowerBound_Sched_lam_polyT
import Theorems.Thm_CircuitLowerBound_Sched_bt_le
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_Groundwork_PolyT_div
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
variable {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hk : Unary fun x => kb (e x)) (hl : Unary fun x => lam (e x)) (hL : Unary L) (hP : PolyT P)
include he hk hl hL
omit hk

theorem solution : Unary fun x => bq (e x) (L x) := by
  have hkb := kb_polyT he
  have hlam := lam_polyT he
  have hLp := hL.poly
  have hnum : PolyT fun x => L x - kb (e x) - lam (e x) - 2 :=
    PolyT.sub (PolyT.sub (PolyT.sub hLp hkb) hlam) (PolyT.const 2)
  exact (Unary.of_le hL (PolyT.div hnum (PolyT.const 2)) fun x => bt_le _ _).add hl
