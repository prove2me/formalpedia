-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:16.485216+00:00
-- url     : https://prove2.me/submissions/37df2752-bb1c-40e1-bc76-07fd7a80b55b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_prod_ev_cast_le
import Theorems.Thm_ClauseBound_ParityChecks_Approx_omega_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (ε : ℚ)
    (hε : ∀ u ≤ Fintype.card E, |(1 - 2 * pr nb) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (u.choose i : ℚ)| ≤ ε) :
    |tUpar V nb r i₀ j Λ D - Upar V nb r j Λ D| ≤ 1 / 2 * ε * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 (Nat.zero_le _))
  have hc0 : (0 : ℚ) ≤ (5 / 8) ^ (r - 1 - j) := by positivity
  have hc1 : (5 / 8 : ℚ) ^ (r - 1 - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hterm : ∀ ξ : X,
      |(omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
          (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * ((#(D ∩ V ξ)).choose i : ℚ))) -
        (omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
          (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * (1 - 2 * pr nb) ^ #(D ∩ V ξ)))| ≤
        ((Fintype.card E).choose (nb + 1) : ℚ) * 1 * (1 / 2 * (1 * ε)) := by
    intro ξ
    have h1 : |(omega V nb ξ : ℚ)| ≤ ((Fintype.card E).choose (nb + 1) : ℚ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast omega_le V nb ξ
    have h2 := abs_prod_ev_cast_le (range j) fun j' => #(Λ j' ∩ V ξ)
    have h3 : |(1 / 2 : ℚ)| ≤ 1 / 2 := by rw [abs_of_nonneg (by norm_num)]
    have h4 : |(-1 : ℚ) ^ #(Λ j ∩ V ξ)| ≤ 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    have h5 : |∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * ((#(D ∩ V ξ)).choose i : ℚ) - (1 - 2 * pr nb) ^ #(D ∩ V ξ)| ≤ ε := by
      rw [abs_sub_comm]
      exact hε _ (Finset.card_le_univ _)
    rw [← mul_sub, ← mul_sub, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_mul, abs_mul, abs_mul]
    gcongr
  unfold tUpar Upar
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hc0]
  calc (5 / 8 : ℚ) ^ (r - 1 - j) * |∑ ξ : X, _| ≤ 1 * ∑ _ξ : X, ((Fintype.card E).choose (nb + 1) : ℚ) * 1 * (1 / 2 * (1 * ε)) :=
        mul_le_mul hc1 ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ _ => hterm ξ)) (abs_nonneg _) zero_le_one
    _ = 1 / 2 * ε * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring
end ClauseBound.ParityChecks.Approx
