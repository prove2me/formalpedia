-- Prove2me | solution 1 for ExplicitCost.g_add_K_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:35.335309+00:00
-- url     : https://prove2.me/submissions/0487348e-c78e-4a29-a0ba-fb6006c5b92d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_K_le_g
import Theorems.Thm_ExplicitCost_two_pow_le_g
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution {x₀ : ℕ} (hx : 1 ≤ x₀) (j : ℕ) : g x₀ j + K x₀ j ^ 2 ≤ g x₀ j ^ 4 := by
  have hp : 2 ^ 1 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx
  have hg : 2 ≤ g x₀ j := le_trans hp (two_pow_le_g x₀ j)
  have h1 : K x₀ j ^ 2 ≤ g x₀ j ^ 2 := Nat.pow_le_pow_left (K_le_g x₀ j) 2
  have h2 : g x₀ j ≤ g x₀ j ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : 2 ^ 2 ≤ g x₀ j ^ 2 := Nat.pow_le_pow_left hg 2
  have h4 : g x₀ j ^ 4 = g x₀ j ^ 2 * g x₀ j ^ 2 := by ring
  have h5 := Nat.mul_le_mul_right (g x₀ j ^ 2) h3
  omega
end ExplicitCost
