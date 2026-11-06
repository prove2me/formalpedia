-- Prove2me | solution 1 for ExplicitCost.c_le_e_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:33.477252+00:00
-- url     : https://prove2.me/submissions/087b7d78-a2ad-4adb-98ba-40a952c634f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RoomWithin
import Theorems.Thm_Eight_Level_rho_ge


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed Finset
namespace ExplicitCost
theorem _root_.solution (hLv : ChainLevels) (hA : Levels.Gen.PartA) {ρ : ℝ} {c x₀ lam B : ℕ} (hN : Numbers ρ c x₀ lam B) (j : ℕ) : (c : ℝ) ≤ e ρ x₀ j * (K x₀ j : ℝ) ^ 2 := by
  have h1 := (hLv c x₀ j j hN.x₀_ge hN.x₀_c le_rfl).1
  rw [Nat.sub_self] at h1
  have h2 : ((2 : ℝ) ^ j * ((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) ≤ (K x₀ j : ℝ) ^ 2 := by exact_mod_cast h1
  have h3 := hA.e_ge ρ x₀ j hN.rho_ge hN.rho_lt hN.x₀_ge
  have h4 : (1 / 2 : ℝ) ^ j ≤ ρ ^ j := pow_le_pow_left₀ (by norm_num) hN.rho_ge j
  have h5 : (1 : ℝ) ≤ ((c : ℝ) + 5) ^ j := one_le_pow₀ (by have : (0 : ℝ) ≤ c := Nat.cast_nonneg _
                                                           linarith)
  have h6 : ((c : ℝ) + 5) ≤ (2 : ℝ) ^ x₀ := by exact_mod_cast hN.x₀_c
  have h7 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have h8 : 2 * (c : ℝ) ≤ ((2 : ℝ) ^ x₀) ^ 2 := by nlinarith
  have h9 : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hq : (0 : ℝ) ≤ ((2 : ℝ) ^ x₀) ^ 2 := by positivity
  calc (c : ℝ) ≤ ((2 : ℝ) ^ x₀) ^ 2 / 2 := by linarith
    _ ≤ (((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) / 2 := by
        have := mul_le_mul_of_nonneg_right h5 hq
        linarith
    _ = (1 / 2 : ℝ) ^ j / 2 * ((2 : ℝ) ^ j * ((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) := by
        have : (1 / 2 : ℝ) ^ j / 2 * ((2 : ℝ) ^ j * ((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) = ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) * ((((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) / 2) := by ring
        rw [this, h9, one_mul]
    _ ≤ e ρ x₀ j * (K x₀ j : ℝ) ^ 2 := mul_le_mul (by linarith) h2 (by positivity) (by linarith)
end ExplicitCost
