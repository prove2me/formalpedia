-- Prove2me | solution 1 for Eight.sigma_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:54.867615+00:00
-- url     : https://prove2.me/submissions/2e241b0d-d1ac-467e-a412-3fe3ec4d6890

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
theorem _root_.solution (p q : Block) : sigma p q * sigma p q = 1 := by
  rcases sigma_eq_or p q with h | h <;> rw [h] <;> norm_num
end Eight
