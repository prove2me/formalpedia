-- Prove2me | solution 1 for ExplicitCost.two_mul_pow_mul_K_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:42.158826+00:00
-- url     : https://prove2.me/submissions/5db32f74-0ee7-4f96-a897-d489aa3e2587

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_two_pow_mul_K_le_g
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_ExplicitCost_K_pos
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution {x₀ : ℕ} (hx : 1 ≤ x₀) (j : ℕ) : 2 * (2 ^ x₀ * K x₀ j ^ 2) ≤ g x₀ j ^ 4 := by
  have hp : 2 ≤ 2 ^ x₀ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx
  have h0 : 1 ≤ 2 ^ x₀ * K x₀ j := Nat.mul_pos (by omega) (K_pos x₀ j)
  have h1 : 2 * (2 ^ x₀ * K x₀ j ^ 2) ≤ (2 ^ x₀ * K x₀ j) ^ 2 := by
    have e : (2 ^ x₀ * K x₀ j) ^ 2 = 2 ^ x₀ * (2 ^ x₀ * K x₀ j ^ 2) := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ hp
  have h2 : (2 ^ x₀ * K x₀ j) ^ 2 ≤ (2 ^ x₀ * K x₀ j) ^ 4 := Nat.pow_le_pow_right h0 (by norm_num)
  exact (h1.trans h2).trans (Nat.pow_le_pow_left (two_pow_mul_K_le_g x₀ j) 4)
end ExplicitCost
