-- Prove2me | solution 1 for ExplicitCost.countBaseFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:51.974203+00:00
-- url     : https://prove2.me/submissions/6e2f09fe-3a7b-4261-9c2c-d6cd0780e53b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountBase
import Theorems.Thm_ExplicitCost_base_count
import Theorems.Thm_ExplicitCost_baseAt_cast
import Theorems.Thm_ExplicitCost_pos_of_chainLabel
import Theorems.Thm_GeneralPieces_Rate_brute_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution : CountBaseFrom := by
  intro hL C ρ c x₀ C₀ l lam B t hN hC ht
  obtain ⟨hΛ, hBB⟩ := pos_of_chainLabel hL hN (Nat.zero_le l)
  have hk : 2 ^ 1 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) (by have := hN.x₀_ge; omega)
  have hX : 2 * 2 ^ x₀ ≤ baseAt ρ c x₀ l lam B 0 := by
    have : 2 ^ x₀ * 2 ≤ 2 ^ x₀ * (lamAt ρ c x₀ l lam B 0 + bitsAt ρ c x₀ l lam B 0) := Nat.mul_le_mul_left _ (by omega)
    change 2 * 2 ^ x₀ ≤ 2 ^ x₀ * (lamAt ρ c x₀ l lam B 0 + bitsAt ρ c x₀ l lam B 0)
    omega
  have hn : 2 ≤ C₀ * K x₀ 0 ^ 2 := by
    have h1 : 2 ^ 2 ≤ (2 ^ x₀) ^ 2 := Nat.pow_le_pow_left hk 2
    have h2 : 1 * (2 ^ x₀) ^ 2 ≤ C₀ * (2 ^ x₀) ^ 2 := Nat.mul_le_mul_right _ hC
    change 2 ≤ C₀ * (2 ^ x₀) ^ 2
    omega
  have h := base_count (A := 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0)) (by omega : 1 ≤ 2 ^ x₀) hX hn ht
  have h' : solverCost C ρ c x₀ l lam B 0 0 t ≤ t * (2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * baseAt ρ c x₀ l lam B 0 ^ (C₀ * K x₀ 0 ^ 2)) := h
  have hr : (solverCost C ρ c x₀ l lam B 0 0 t : ℝ) ≤ t * ((2 : ℝ) ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * (baseAt ρ c x₀ l lam B 0 : ℝ) ^ (C₀ * K x₀ 0 ^ 2)) := by exact_mod_cast h'
  refine hr.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  unfold levelBound timeBound
  rw [baseAt_cast]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← Real.rpow_natCast (2 : ℝ) (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (GeneralPieces.Rate.brute_le ρ x₀ (lamAt ρ c x₀ l lam B 0))
end ExplicitCost
