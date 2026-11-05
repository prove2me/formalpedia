-- Prove2me | solution 1 for Eight.Rb_add_Cb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:52:03.772697+00:00
-- url     : https://prove2.me/submissions/2744a30f-2672-4c52-9898-18f9d672b944

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_bxor_right_cancel
import Theorems.Thm_Eight_Rb_of_ne
import Theorems.Thm_Eight_Cb_of_ne
import Theorems.Thm_Eight_not_cross_of_ne
import Theorems.Thm_Eight_Rb_diag
import Theorems.Thm_Eight_Cb_diag
import Theorems.Thm_Eight_Rb_add_Cb_of_ne

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (hS : Signs) (x y u v : Block) : Rb x y u v + Cb x y u v = 2 * if x = v ∧ y = u then 1 else 0 := by
  by_cases h : bxor x y = bxor v u
  · by_cases hyu : y = u
    · subst hyu
      obtain rfl : x = v := bxor_right_cancel h
      rw [Rb_diag, Cb_diag]; simp
    · rw [Rb_add_Cb_of_ne hS h hyu, if_neg fun h' => hyu h'.2]; rfl
  · rw [Rb_of_ne h, Cb_of_ne h, if_neg (not_cross_of_ne h)]; rfl
end Eight
