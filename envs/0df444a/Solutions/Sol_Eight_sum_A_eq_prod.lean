-- Prove2me | solution 1 for Eight.sum_A_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:39.246188+00:00
-- url     : https://prove2.me/submissions/ef733a05-987a-40af-8a9b-541c600d2c8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_natDegree_prodRC_le

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution {lam : ℕ} (x y u v : Pieces.Bits lam) :
    ∑ i ∈ range (tOf lam + 1), A lam i x y u v =
      ∏ s ∈ range (tOf lam), (Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) + Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)) := by
  have h := eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_prodRC_le x y u v)) (1 : ℤ)
  simp only [one_pow, mul_one] at h
  rw [show ∑ i ∈ range (tOf lam + 1), A lam i x y u v = ∑ i ∈ range (tOf lam + 1), (prodRC x y u v).coeff i from rfl, ← h, prodRC, eval_prod]
  simp
end Eight
