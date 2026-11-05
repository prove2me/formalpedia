-- Prove2me | solution 1 for Eight.abs_Rb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:52:38.154503+00:00
-- url     : https://prove2.me/submissions/9892e33a-4baf-4bff-9b6a-dc74ef241035

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_Rb_val

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (x y u v : Block) : |Rb x y u v| ≤ 1 := by
  rcases Rb_val x y u v with h | h | h <;> rw [h] <;> norm_num
end Eight
