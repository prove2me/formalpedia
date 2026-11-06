-- Prove2me | solution 1 for ExplicitCost.levelBound_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:08.727122+00:00
-- url     : https://prove2.me/submissions/6a2f145c-f4b7-4403-a6c2-afe488dc2d64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_pos_of_chainLabel
import Theorems.Thm_ExplicitCost_four_mul_le_xiAt
import Theorems.Thm_ExplicitCost_four_mul_div_g
import Theorems.Thm_ExplicitCost_levelBound_succ
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_ExplicitCost_K_pos
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hL : ChainLabel) (hBl : BoundBelow) (hEF : ExponentFits) (hN : Numbers ρ c x₀ lam B) (hj : j < l) {C₀ : ℕ} (hC : 2 * (c + 1) ≤ C₀) :
    levelBound ρ c x₀ C₀ l lam B j ≤ levelBound ρ c x₀ C₀ l lam B (j + 1) := by
  refine (hBl ρ c x₀ C₀ l lam B j hN hj).trans ?_
  rw [levelBound_succ]
  obtain ⟨-, hBB⟩ := pos_of_chainLabel hL hN (by omega : j + 1 ≤ l)
  have hx1 : 1 ≤ x₀ := by have := hN.x₀_ge; omega
  have hXn := four_mul_le_xiAt hx1 ρ c l lam B j hBB
  have hX1 : (1 : ℝ) ≤ (xiAt ρ c x₀ l lam B j : ℝ) := by exact_mod_cast (by omega : 1 ≤ xiAt ρ c x₀ l lam B j)
  have hK : (0 : ℝ) < K x₀ j := by exact_mod_cast K_pos x₀ j
  have h1 := hEF c 0 C₀ x₀ j hN.x₀_ge hN.x₀_c (by omega)
  have h2 : c * (g x₀ j ^ 4 / 4) ≤ c * g x₀ j ^ 4 / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := four_mul_div_g hx1 j
    calc c * (g x₀ j ^ 4 / 4) * 2 ≤ c * (4 * (g x₀ j ^ 4 / 4)) := by nlinarith [Nat.zero_le (c * (g x₀ j ^ 4 / 4))]
      _ = c * g x₀ j ^ 4 := by rw [this]
  refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (pow_le_pow_right₀ hX1 (by omega)) (by positivity) (by positivity)
  have : (0 : ℝ) ≤ 3 * ((K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / K x₀ j := by positivity
  linarith
end ExplicitCost
