-- Prove2me | solution 1 for Eight.bxor_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:03.601186+00:00
-- url     : https://prove2.me/submissions/16e282c5-8eb2-4417-9747-5ddcc6ccea81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
import Theorems.Thm_Eight_block_ext

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p : Block) : bxor p p = (false, false, false) := block_ext (Bool.xor_self _) (Bool.xor_self _) (Bool.xor_self _)
end Eight
