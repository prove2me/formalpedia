-- Prove2me | solution 1 for ClauseBound.Grid.card_labels_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:22.591319+00:00
-- url     : https://prove2.me/submissions/183f24c0-ed92-4bea-9dd3-ae6aabc31084

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_Groundwork_card_tuples


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {d L : ℕ} (hγ : Fintype.card γ = d) (hα : Fintype.card α = 2 ^ L)
    (S : γ × γ → Finset τ) (e : γ × γ → ℕ) (h : ∀ k, #(S k) ≤ 2 ^ e k) (t₀ : τ) :
    #((univ : Finset (γ → α)) ×ˢ tuples (fun k : γ × γ => k.1 < k.2) S t₀) ≤
      2 ^ (d * L + ∑ k : γ × γ with k.1 < k.2, e k) := by
  rw [card_product, card_univ, Fintype.card_fun, hα, hγ, ← pow_mul, card_tuples, pow_add, ← prod_pow_eq_pow_sum,
    Nat.mul_comm L d]
  exact Nat.mul_le_mul_left _ (prod_le_prod (fun _ _ => Nat.zero_le _) fun k _ => h k)
end ClauseBound.Grid
