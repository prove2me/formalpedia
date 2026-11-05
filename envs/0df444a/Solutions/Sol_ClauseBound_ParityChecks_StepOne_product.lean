-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:16.408955+00:00
-- url     : https://prove2.me/submissions/e1d90f99-a9f5-4cc9-874c-43c2a827e519

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Theorems.Thm_P2M_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_one__f4c3a51312ce

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution {X E : Type} [DecidableEq E] (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E) (hG : ∀ ξ, nb < #(V ξ) → ∃ j < r, Odd #(Λ j ∩ V ξ))
    (ξ : X) : (∑ S ∈ (V ξ).powerset with #S ≤ nb, (-1 : ℤ) ^ #S) * ∏ j ∈ range r, ev #(Λ j ∩ V ξ) = if V ξ = ∅ then 1 else 0 := by
  by_cases h0 : V ξ = ∅
  · rw [if_pos h0, h0, powerset_empty, filter_true_of_mem (fun S hS => by rw [mem_singleton.1 hS, card_empty]; exact Nat.zero_le _),
      sum_singleton, card_empty, pow_zero, one_mul]
    exact prod_eq_one fun j _ => by rw [inter_empty, card_empty]; rfl
  · rw [if_neg h0]
    rcases Nat.lt_or_ge nb #(V ξ) with h | h
    · obtain ⟨j, hj, hodd⟩ := hG ξ h
      rw [prod_eq_zero (mem_range.2 hj) (by rw [ev, if_neg (Nat.not_even_iff_odd.2 hodd)]), mul_zero]
    · rw [filter_true_of_mem fun S hS => (card_le_card (mem_powerset.1 hS)).trans h, sum_powerset_neg_one' h0, zero_mul]
end ClauseBound.ParityChecks.StepOne
