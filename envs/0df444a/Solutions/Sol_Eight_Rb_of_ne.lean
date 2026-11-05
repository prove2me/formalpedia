-- Prove2me | solution 1 for Eight.Rb_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:57.164111+00:00
-- url     : https://prove2.me/submissions/ce43b3da-2eca-4c17-a1df-32edeaaa86ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_Rb_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {x y u v : Block} (h : bxor x y ≠ bxor v u) : Rb x y u v = 0 := by rw [Rb_eq, if_neg h]
end Eight
