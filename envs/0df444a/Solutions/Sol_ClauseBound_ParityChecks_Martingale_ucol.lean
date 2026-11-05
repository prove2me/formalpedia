-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.ucol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:11:34.261878+00:00
-- url     : https://prove2.me/submissions/6cf08bed-3bf1-4bdb-b6c7-918a941263f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_one_add_pr_ne
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_average
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_col_putIn_self
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_col_putIn_ne

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Ucol nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ucol nb r j Λ (D.erase e) = Ucol nb r j Λ D := by
  unfold Ucol
  rw [mul_left_comm (pr nb), mul_left_comm (1 - pr nb), ← mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun e' _ => ?_
  by_cases hee : e' = e
  · subst hee
    have hj := hS.j_lt
    have h1 : undCol r j D e' = r - 1 - j + 1 := by simp [undCol, he]
    have h2 : undCol r j (D.erase e') e' = r - 1 - j := by simp [undCol]
    have hk : r - (r - 1 - j) = r - (r - 1 - j + 1) + 1 := by omega
    rw [card_col_putIn_self hS he, h1, h2, hk, pow_succ' (2 : ℚ)]
    exact average _ _ _ (one_add_pr_ne nb)
  · have h1 : undCol r j (D.erase e) e' = undCol r j D e' := by simp [undCol, hee]
    rw [card_col_putIn_ne r j Λ hee, h1]
    ring
end ClauseBound.ParityChecks.Martingale
