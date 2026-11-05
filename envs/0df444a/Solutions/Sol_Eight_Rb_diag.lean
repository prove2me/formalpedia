-- Prove2me | solution 1 for Eight.Rb_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:48:43.162485+00:00
-- url     : https://prove2.me/submissions/22596666-448a-4e07-b615-75c60fc7d372

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_sigma_mul_self
import Theorems.Thm_Eight_Rb_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (x y : Block) : Rb x y y x = 1 := by rw [Rb_eq, if_pos rfl, sigma_mul_self]
end Eight
