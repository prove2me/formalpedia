-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.card_col_putIn_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:29.201809+00:00
-- url     : https://prove2.me/submissions/ab793d6c-44be-4218-8c08-22e451292c02

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_putIn_same
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_putIn_ne

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution (r j : ℕ) (Λ : ℕ → Finset E) {e e' : E} (h : e' ≠ e) :
    #{j' ∈ range r | e' ∈ putIn j Λ e j'} = #{j' ∈ range r | e' ∈ Λ j'} := by
  congr 1
  refine filter_congr fun j' _ => ?_
  by_cases hjj : j' = j
  · subst hjj
    simp [putIn_same, h]
  · rw [putIn_ne hjj]
end ClauseBound.ParityChecks.Martingale
