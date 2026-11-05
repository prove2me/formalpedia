-- Prove2me | solution 1 for Eight.bxor_bxor_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:45:30.017197+00:00
-- url     : https://prove2.me/submissions/7651a259-7ebd-4328-bbec-f4201e10ed7c

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
import Theorems.Thm_Eight_bxor_assoc
import Theorems.Thm_Eight_bxor_self
import Theorems.Thm_Eight_bxor_zero

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p d : Block) : bxor (bxor p d) d = p := by rw [bxor_assoc, bxor_self, bxor_zero]
end Eight
