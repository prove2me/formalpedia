-- Prove2me | solution 1 for Eight.sigma_eq_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:00:20.874765+00:00
-- url     : https://prove2.me/submissions/0dae1cbe-b58a-46af-ace8-e4f3cb67b364

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p q : Block) : sigma p q = 1 ∨ sigma p q = -1 := neg_one_pow_eq_or ℤ _
end Eight
