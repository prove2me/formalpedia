-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.sum_undRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:19.946315+00:00
-- url     : https://prove2.me/submissions/80ea145a-552c-4c0f-9658-e44b2fc24ce7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_eq_succ
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_undRow_self
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_undRow_ne

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution {r j : ℕ} {D : Finset E} {e : E} (hj : j < r) (he : e ∈ D) :
    ∑ j' ∈ range r, undRow j D j' = ∑ j' ∈ range r, undRow j (D.erase e) j' + 1 := by
  have hj : j ∈ range r := mem_range.2 hj
  have h1 : ∑ j' ∈ range r, undRow j D j' = undRow j D j + ∑ j' ∈ (range r).erase j, undRow j D j' := (add_sum_erase _ _ hj).symm
  have h2 : ∑ j' ∈ range r, undRow j (D.erase e) j' = undRow j (D.erase e) j + ∑ j' ∈ (range r).erase j, undRow j (D.erase e) j' :=
    (add_sum_erase _ _ hj).symm
  have h3 : ∑ j' ∈ (range r).erase j, undRow j D j' = ∑ j' ∈ (range r).erase j, undRow j (D.erase e) j' :=
    sum_congr rfl fun j' hj' => undRow_ne (ne_of_mem_erase hj') D (D.erase e)
  rw [h1, h2, h3, undRow_self, undRow_self, card_eq_succ he]
  omega
end ClauseBound.ParityChecks.Martingale
