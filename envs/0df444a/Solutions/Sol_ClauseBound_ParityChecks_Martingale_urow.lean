-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.urow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:20.975524+00:00
-- url     : https://prove2.me/submissions/4ab497f9-e50b-499c-aa4f-382b98eb44e1

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
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_one_add_pr_ne
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_notMem_of_mem
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_eq_succ
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_average
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_undRow_self
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_undRow_ne

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Urow nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Urow nb r j Λ (D.erase e) = Urow nb r j Λ D := by
  unfold Urow
  rw [mul_left_comm (pr nb), mul_left_comm (1 - pr nb), ← mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j' _ => ?_
  by_cases hjj : j' = j
  · subst hjj
    have hD := card_eq_succ he
    have hle : #D ≤ Fintype.card E := card_le_univ D
    have hk : Fintype.card E - #(D.erase e) = Fintype.card E - #D + 1 := by omega
    rw [putIn_same, card_insert_of_notMem (notMem_of_mem hS he), undRow_self, undRow_self, hk, pow_succ' (2 : ℚ)]
    exact average _ _ _ (one_add_pr_ne nb)
  · rw [putIn_ne hjj, undRow_ne hjj (D.erase e) D]
    ring
end ClauseBound.ParityChecks.Martingale
