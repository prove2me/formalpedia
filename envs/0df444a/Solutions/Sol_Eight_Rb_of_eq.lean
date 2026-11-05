-- Prove2me | solution 1 for Eight.Rb_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:44.358215+00:00
-- url     : https://prove2.me/submissions/217dfbc9-0994-4951-91b1-f9e3ef718f2c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_sigma_mul_eq_or
import Theorems.Thm_Eight_Rb_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {x y u v : Block} (h : bxor x y = bxor v u) : Rb x y u v = 1 ∨ Rb x y u v = -1 := by
  rw [Rb_eq, if_pos h]; exact sigma_mul_eq_or _ _ _ _
end Eight
