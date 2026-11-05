-- Prove2me | solution 1 for Eight.sigma_mul_eq_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:48:15.51211+00:00
-- url     : https://prove2.me/submissions/111d0f6f-29e1-45ec-bd9d-cea1ecb4b8df

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
theorem _root_.solution (p q p' q' : Block) : sigma p q * sigma p' q' = 1 ∨ sigma p q * sigma p' q' = -1 := by
  rcases sigma_eq_or p q with h | h <;> rcases sigma_eq_or p' q' with h' | h' <;> rw [h, h'] <;> norm_num
end Eight
