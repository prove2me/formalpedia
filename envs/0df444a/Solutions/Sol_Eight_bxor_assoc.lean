-- Prove2me | solution 1 for Eight.bxor_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:00:17.937781+00:00
-- url     : https://prove2.me/submissions/6efa0d71-f269-44af-b4f8-d64947efc264

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
theorem _root_.solution (p q r : Block) : bxor (bxor p q) r = bxor p (bxor q r) := block_ext (Bool.xor_assoc _ _ _) (Bool.xor_assoc _ _ _) (Bool.xor_assoc _ _ _)
end Eight
