-- Prove2me | solution 1 for Eight.exists_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:40.70728+00:00
-- url     : https://prove2.me/submissions/7b6e0685-ed4f-48de-b4e8-40d96d71eed4

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
import Theorems.Thm_Eight_bxor_bit2
import Theorems.Thm_Eight_bxor_bit3

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {d : Block} (h : d ≠ (false, false, false)) : d.1 = true ∨ d.2.1 = true ∨ d.2.2 = true := by
  by_contra hn
  simp only [not_or, Bool.not_eq_true] at hn
  exact h (block_ext hn.1 hn.2.1 hn.2.2)
end Eight
