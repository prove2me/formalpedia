-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.martingale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:08.428185+00:00
-- url     : https://prove2.me/submissions/2ef39c89-c889-45a3-9e2a-9c3af4d93363

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_upar
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_uinc
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_urow
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_ucol

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (e : E),
    2 ≤ nb → IsState r j Λ D → e ∈ D →
    pr nb * Ups V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ups V nb r j Λ (D.erase e) = Ups V nb r j Λ D := by
  intro X E _ _ _ V nb r j Λ D e _ hS he
  unfold Ups
  rw [← upar V nb hS he, ← uinc nb hS he, ← urow nb hS he, ← ucol nb hS he]
  ring
end ClauseBound.ParityChecks.Martingale
