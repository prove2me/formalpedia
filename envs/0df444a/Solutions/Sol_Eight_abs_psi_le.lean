-- Prove2me | solution 1 for Eight.abs_psi_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:09.862811+00:00
-- url     : https://prove2.me/submissions/01148b81-6149-4fd7-9cb6-83bb2e36d803

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_sigma_eq_or

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (k p q : Block) : |psi k p q| ≤ 1 := by
  unfold psi
  split_ifs
  · rcases sigma_eq_or p q with h | h <;> rw [h] <;> norm_num
  · norm_num
end Eight
