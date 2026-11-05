-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:05:52.342242+00:00
-- url     : https://prove2.me/submissions/1910711e-6795-4a73-83fb-4c5f30d7a097

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_prod_ev_le
import Theorems.Thm_ClauseBound_ParityChecks_Approx_omega_le
import Theorems.Thm_ClauseBound_ParityChecks_Approx_choose_card_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (V : X → Finset E) (nb i j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) :
    |Aint V nb j Λ| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ∧
      |Bint V nb i j Λ D| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) * (Fintype.card E).choose i : ℕ) := by
  have hw : ∀ ξ : X, |(omega V nb ξ : ℤ)| ≤ ((Fintype.card E).choose (nb + 1) : ℤ) := fun ξ => by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast omega_le V nb ξ
  constructor
  · unfold Aint
    calc |∑ ξ : X, (omega V nb ξ : ℤ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)|
        ≤ ∑ _ξ : X, ((Fintype.card E).choose (nb + 1) : ℤ) * 1 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
          have h1 := hw ξ
          have h2 := abs_prod_ev_le (range j) fun j' => #(Λ j' ∩ V ξ)
          rw [abs_mul]
          gcongr
      _ = (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring
  · unfold Bint
    calc |∑ ξ : X, (omega V nb ξ : ℤ) * ((#(D ∩ V ξ)).choose i : ℤ) * (-1) ^ #(Λ j ∩ V ξ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)|
        ≤ ∑ _ξ : X, ((Fintype.card E).choose (nb + 1) : ℤ) * ((Fintype.card E).choose i : ℤ) * 1 * 1 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
          have h1 := hw ξ
          have h2 := abs_prod_ev_le (range j) fun j' => #(Λ j' ∩ V ξ)
          have h3 : |((#(D ∩ V ξ)).choose i : ℤ)| ≤ ((Fintype.card E).choose i : ℤ) := by
            rw [abs_of_nonneg (Int.natCast_nonneg _)]
            exact_mod_cast choose_card_le (D ∩ V ξ) i
          have h4 : |(-1 : ℤ) ^ #(Λ j ∩ V ξ)| ≤ 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
          rw [abs_mul, abs_mul, abs_mul]
          gcongr
      _ = (Fintype.card X * (Fintype.card E).choose (nb + 1) * (Fintype.card E).choose i : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring
end ClauseBound.ParityChecks.Approx
