-- Prove2me | solution 1 for Eight.bxor_cancel_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:45:36.283405+00:00
-- url     : https://prove2.me/submissions/f12b332c-513a-467c-926c-47aa09aeaea2

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
import Theorems.Thm_Eight_bxor_comm
import Theorems.Thm_Eight_bxor_assoc
import Theorems.Thm_Eight_bxor_self
import Theorems.Thm_Eight_bxor_zero

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p q : Block) : bxor p (bxor p q) = q := by rw [← bxor_assoc, bxor_self, bxor_comm, bxor_zero]
end Eight
