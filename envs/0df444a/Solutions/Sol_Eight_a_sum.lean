-- Prove2me | solution 1 for Eight.a_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:53:35.056745+00:00
-- url     : https://prove2.me/submissions/ff13a08e-65d4-4f81-8902-dd2e82b5bf26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_prod_cross_blocks
import Theorems.Thm_Eight_sum_A_eq_prod
import Theorems.Thm_Eight_Rb_add_Cb


set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution (hS : Signs) : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam,
    ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v := by
  intro lam _ x y u v
  rw [sum_A_eq_prod]
  simp_rw [Rb_add_Cb hS]
  rw [prod_mul_distrib, prod_const, card_range, prod_cross_blocks]
end Eight
