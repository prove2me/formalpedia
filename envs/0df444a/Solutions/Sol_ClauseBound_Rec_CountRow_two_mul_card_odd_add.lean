-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.two_mul_card_odd_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:47:18.643001+00:00
-- url     : https://prove2.me/submissions/5b7d7203-5378-451c-86c3-9aead93d1960

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_prod_sg

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] :
    2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} + 2 ^ Fintype.card ι = Fintype.card (ι → Bool × Bool) := by
  have h1 : ∑ γ : ι → Bool × Bool, ∏ k, sg (γ k) = 2 ^ Fintype.card ι := by
    have h0 : ∑ e : Bool × Bool, sg e = 2 := by decide
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => univ) fun _ e => sg e]
    simp [h0]
  have h2 : ∑ γ : ι → Bool × Bool, ∏ k, sg (γ k)
      = (Fintype.card (ι → Bool × Bool) : ℤ) - 2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} := by
    have h (γ : ι → Bool × Bool) : ∏ k, sg (γ k) = 1 - 2 * if Odd #{k | γ k = (true, true)} then (1 : ℤ) else 0 := by
      rw [prod_sg]; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl fun γ _ => h γ, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp
  rw [h2] at h1
  have h3 : ((2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} + 2 ^ Fintype.card ι : ℕ) : ℤ)
      = (Fintype.card (ι → Bool × Bool) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h3
end ClauseBound.Rec.CountRow
