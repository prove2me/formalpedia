-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.uinc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:10:09.189107+00:00
-- url     : https://prove2.me/submissions/7e2d186e-0c5e-4ee0-9e5f-049c856a0025

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_sum_card_putIn
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_sum_undRow

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Uinc nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Uinc nb r j Λ (D.erase e) = Uinc nb r j Λ D := by
  unfold Uinc
  rw [sum_card_putIn hS he, sum_undRow hS.j_lt he]
  push_cast
  ring
end ClauseBound.ParityChecks.Martingale
