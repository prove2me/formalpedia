-- Prove2me | solution 1 for ExplicitCost.roomIsWithinTheBoundFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:26:43.896648+00:00
-- url     : https://prove2.me/submissions/6365f2e0-4b11-4080-9942-4a5917646202

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RoomWithin
import Theorems.Thm_ExplicitCost_room_le_aux
import Theorems.Thm_ExplicitCost_c_le_e_mul
import Theorems.Thm_ExplicitCost_baseAt_cast
import Theorems.Thm_ExplicitCost_levelBound_le_top
import Theorems.Thm_ExplicitCost_pos_of_chainLabel
import Theorems.Thm_ExplicitCost_two_pow_le_K
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed Finset
namespace ExplicitCost
theorem _root_.solution : RoomIsWithinTheBoundFrom := by
  intro hL hBl hLv hEF hA c
  refine ⟨2 * c + 3, fun ρ x₀ l lam B h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hN : Numbers ρ c x₀ lam B := ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup (range (l + 1)) ⟨0, mem_range.2 (by omega)⟩ fun j => lamAt ρ c x₀ l lam B j
  have hjl : j ≤ l := by have := mem_range.1 hj; omega
  have e1 : lamMax ρ c x₀ l lam B = lamAt ρ c x₀ l lam B j := hmax
  rw [e1]
  refine le_trans ?_ (levelBound_le_top hL hBl hEF hN (by omega : 2 * (c + 1) ≤ 2 * c + 3) l (l - j) j (by omega))
  obtain ⟨hΛ, hBB⟩ := pos_of_chainLabel hL hN hjl
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℕ, Λ = lamAt ρ c x₀ l lam B j := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X : ℕ, X = baseAt ρ c x₀ l lam B j := ⟨_, rfl⟩
  have hK8 : 8 ≤ K x₀ j := by
    have a : 2 ^ 3 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := two_pow_le_K x₀ j
    omega
  have hXK : K x₀ j * (Λ + 1) ≤ X := by rw [hXd, hΛd]; exact Nat.mul_le_mul_left _ (by omega)
  have hX2 : 2 * Λ ≤ X := by
    have : 2 * (Λ + 1) ≤ K x₀ j * (Λ + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hX8 : 8 ≤ X := by
    have : 8 * 1 ≤ K x₀ j * (Λ + 1) := Nat.mul_le_mul hK8 (by omega)
    omega
  have r1 : PiecesCounted.room c Λ ≤ 2 ^ (c * Λ) * X ^ (2 * c + 3) := room_le_aux (Nat.pow_le_pow_left hX2 c) hX8 h3 Nat.one_le_two_pow
  have r2 : (PiecesCounted.room c Λ : ℝ) ≤ (2 : ℝ) ^ (c * Λ) * (X : ℝ) ^ (2 * c + 3) := by exact_mod_cast r1
  rw [← hΛd]
  refine r2.trans ?_
  unfold levelBound timeBound
  rw [baseAt_cast, ← hXd, ← hΛd]
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hKsq : 1 ≤ K x₀ j ^ 2 := Nat.pow_pos (by omega)
  refine mul_le_mul ?_ (pow_le_pow_right₀ hX1 (Nat.le_mul_of_pos_right _ hKsq)) (by positivity) (by positivity)
  rw [← Real.rpow_natCast (2 : ℝ) (c * Λ)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  push_cast
  exact mul_le_mul_of_nonneg_right (c_le_e_mul hLv hA hN j) (Nat.cast_nonneg _)
end ExplicitCost
