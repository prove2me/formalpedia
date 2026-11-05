-- Prove2me | solution 1 for Eight.Rb_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:55.618965+00:00
-- url     : https://prove2.me/submissions/0f6afe2c-ff31-4519-891b-72d632ebceb8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_sum_psi_mul

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (x y u v : Block) : Rb x y u v = if bxor x y = bxor v u then sigma x y * sigma v u else 0 := sum_psi_mul x y v u
end Eight
