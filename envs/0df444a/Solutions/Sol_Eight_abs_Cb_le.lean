-- Prove2me | solution 1 for Eight.abs_Cb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:54:58.883306+00:00
-- url     : https://prove2.me/submissions/b6d39c6b-e126-4e42-873e-689fb1f53bb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_abs_Rb_le

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (x y u v : Block) : |Cb x y u v| ≤ 1 := abs_Rb_le x u y v
end Eight
