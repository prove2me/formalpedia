-- Prove2me | solution 1 for ExplicitCost.exponentFits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:54:01.322933+00:00
-- url     : https://prove2.me/submissions/79486e77-0f41-4871-9af8-9e3530c9d0e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_K_succ_sq
import Theorems.Thm_ExplicitCost_g_pos
import Theorems.Thm_ExplicitCost_two_mul_c_mul_K_sq_le
import Theorems.Thm_ExplicitCost_g_add_K_sq_le

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution : ExponentFits := by
  intro c C₄ C₀ x₀ j hx hc hC
  rw [K_succ_sq]
  have hk := two_mul_c_mul_K_sq_le (by omega) hc j
  have hG := g_add_K_sq_le (x₀ := x₀) (by omega) j
  have hg : 1 ≤ g x₀ j ^ 4 := Nat.pow_pos (g_pos x₀ j)
  have h1 : c * g x₀ j ^ 4 / 2 ≤ c * g x₀ j ^ 4 := Nat.div_le_self _ _
  have h2 : C₄ ≤ C₄ * g x₀ j ^ 4 := Nat.le_mul_of_pos_right _ hg
  have h3 : 2 * (c * g x₀ j ^ 4 + C₄ * g x₀ j ^ 4 + g x₀ j ^ 4) ≤ C₀ * g x₀ j ^ 4 := by
    have := Nat.mul_le_mul_right (g x₀ j ^ 4) hC
    have e : 2 * (c + C₄ + 1) * g x₀ j ^ 4 = 2 * (c * g x₀ j ^ 4 + C₄ * g x₀ j ^ 4 + g x₀ j ^ 4) := by ring
    omega
  have h4 : 2 * ((c + 5) * C₀ * K x₀ j ^ 2) ≤ C₀ * g x₀ j ^ 4 := by
    have := Nat.mul_le_mul_left C₀ hk
    have e : C₀ * (2 * ((c + 5) * K x₀ j ^ 2)) = 2 * ((c + 5) * C₀ * K x₀ j ^ 2) := by ring
    omega
  omega
end ExplicitCost
