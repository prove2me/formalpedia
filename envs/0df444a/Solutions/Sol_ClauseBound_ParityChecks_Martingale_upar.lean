-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.upar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:01.949212+00:00
-- url     : https://prove2.me/submissions/a4d1594c-4cab-49a3-89aa-58e0345871c7

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
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_eq_succ

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution (V : X → Finset E) (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Upar V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Upar V nb r j Λ (D.erase e) = Upar V nb r j Λ D := by
  have hej := notMem_of_mem hS he
  unfold Upar
  rw [mul_left_comm (pr nb), mul_left_comm (1 - pr nb), ← mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun ξ _ => ?_
  have hprod : ∏ j' ∈ range j, (ev #(putIn j Λ e j' ∩ V ξ) : ℚ) = ∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ) :=
    prod_congr rfl fun j' hj' => by rw [putIn_ne (ne_of_lt (mem_range.1 hj'))]
  rw [hprod, putIn_same]
  by_cases hv : e ∈ V ξ
  · have h1 : #(insert e (Λ j) ∩ V ξ) = #(Λ j ∩ V ξ) + 1 := by
      rw [insert_inter_of_mem hv, card_insert_of_notMem fun h => hej (mem_inter.1 h).1]
    have h2 : #(D ∩ V ξ) = #(D.erase e ∩ V ξ) + 1 := by
      rw [erase_inter]
      exact card_eq_succ (mem_inter.2 ⟨he, hv⟩)
    rw [h1, h2]
    ring
  · have h1 : insert e (Λ j) ∩ V ξ = Λ j ∩ V ξ := insert_inter_of_notMem hv
    have h2 : D.erase e ∩ V ξ = D ∩ V ξ := by
      rw [erase_inter, erase_eq_of_notMem fun h => hv (mem_inter.1 h).2]
    rw [h1, h2]
    ring
end ClauseBound.ParityChecks.Martingale
