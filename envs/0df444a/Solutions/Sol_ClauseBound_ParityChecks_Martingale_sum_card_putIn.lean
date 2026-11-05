-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.sum_card_putIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:05.044419+00:00
-- url     : https://prove2.me/submissions/d92fcd62-cc0e-440f-9502-dec340da18ef

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
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_notMem_of_mem

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    ∑ j' ∈ range r, #(putIn j Λ e j') = ∑ j' ∈ range r, #(Λ j') + 1 := by
  have hj : j ∈ range r := mem_range.2 hS.j_lt
  rw [← add_sum_erase _ _ hj, ← add_sum_erase (range r) (fun j' => #(Λ j')) hj, putIn_same, card_insert_of_notMem (notMem_of_mem hS he),
    sum_congr rfl fun j' hj' => by rw [putIn_ne (ne_of_mem_erase hj')]]
  omega
end ClauseBound.ParityChecks.Martingale
