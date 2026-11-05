-- Prove2me | solution 1 for Eight.Rb_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:24.799971+00:00
-- url     : https://prove2.me/submissions/b3ad5287-8cba-42c9-aa8a-37d0b3bd727e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_Rb_of_ne
import Theorems.Thm_Eight_Rb_of_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (x y u v : Block) : Rb x y u v = -1 ∨ Rb x y u v = 0 ∨ Rb x y u v = 1 := by
  by_cases h : bxor x y = bxor v u
  · rcases Rb_of_eq h with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · exact Or.inr (Or.inl (Rb_of_ne h))
end Eight
