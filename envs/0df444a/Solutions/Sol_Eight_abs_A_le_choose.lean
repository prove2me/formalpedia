-- Prove2me | solution 1 for Eight.abs_A_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:06.4048+00:00
-- url     : https://prove2.me/submissions/a79bc4bb-786d-4855-b5e2-f22d921c76f8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_A_eq_sum_subsets
import Theorems.Thm_Eight_abs_Cb_le
import Theorems.Thm_Eight_abs_Rb_le


set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution (lam i : ℕ) (x y u v : Pieces.Bits lam) : |A lam i x y u v| ≤ ((tOf lam).choose i : ℤ) := by
  rw [A_eq_sum_subsets]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ Q ∈ (range (tOf lam)).powersetCard i, |∏ s ∈ range (tOf lam),
      if s ∈ Q then Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) else Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)| ≤ 1 := by
    intro Q _
    rw [abs_prod]
    refine prod_le_one (fun _ _ => abs_nonneg _) fun s _ => ?_
    split_ifs
    · exact abs_Cb_le _ _ _ _
    · exact abs_Rb_le _ _ _ _
  simpa using sum_le_card_nsmul _ _ 1 h
end Eight
