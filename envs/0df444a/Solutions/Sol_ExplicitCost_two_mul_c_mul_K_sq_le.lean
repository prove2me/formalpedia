-- Prove2me | solution 1 for ExplicitCost.two_mul_c_mul_K_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:38.399975+00:00
-- url     : https://prove2.me/submissions/0e85f551-4348-4d02-b1cf-e90a687b1642

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_two_mul_pow_mul_K_sq_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution {c x₀ : ℕ} (hx : 1 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (j : ℕ) : 2 * ((c + 5) * K x₀ j ^ 2) ≤ g x₀ j ^ 4 :=
  (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hc)).trans (two_mul_pow_mul_K_sq_le hx j)
end ExplicitCost
