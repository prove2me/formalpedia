-- Prove2me | solution 1 for ClauseBound.Part.Lower.cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:31:08.349812+00:00
-- url     : https://prove2.me/submissions/ec1df427-0d5d-440a-9eba-ff603da62c33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution (v : ℕ) : (v : ℝ) ^ 3 ≤ 6 * ((v + 3).choose 3 : ℝ) := by
  have h1 : (v + 3 + 1 - 3) ^ 3 ≤ (v + 3).descFactorial 3 := Nat.pow_sub_le_descFactorial _ _
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : v ^ 3 ≤ (v + 3 + 1 - 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : v ^ 3 ≤ 6 * (v + 3).choose 3 := h2.trans h1
  exact_mod_cast h3
end ClauseBound.Part.Lower
