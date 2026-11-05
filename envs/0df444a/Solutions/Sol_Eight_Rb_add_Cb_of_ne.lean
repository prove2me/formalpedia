-- Prove2me | solution 1 for Eight.Rb_add_Cb_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:20.304811+00:00
-- url     : https://prove2.me/submissions/f93e6194-2ad2-4e40-8a57-04758d1b51a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_bxor_eq_swap
import Theorems.Thm_Eight_Rb_eq
import Theorems.Thm_Eight_Cb_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (hS : Signs) {x y u v : Block} (h : bxor x y = bxor v u) (hyu : y ≠ u) : Rb x y u v + Cb x y u v = 0 := by
  rw [Rb_eq, Cb_eq, if_pos h, if_pos ((bxor_eq_swap x y u v).1 h)]
  exact hS x y v u h hyu
end Eight
