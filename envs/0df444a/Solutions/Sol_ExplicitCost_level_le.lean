-- Prove2me | solution 1 for ExplicitCost.level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:07.663393+00:00
-- url     : https://prove2.me/submissions/8f119e0d-d23c-4cb8-91a6-90f40889d462

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_pos_of_chainLabel
import Theorems.Thm_ExplicitCost_baseAt_cast
import Theorems.Thm_ExplicitCost_four_mul_le_xiAt
import Theorems.Thm_ExplicitCost_four_mul_div_g
import Theorems.Thm_ExplicitCost_K_succ_sq


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hL : ChainLabel) (hB : ChainBase) (hE : ChainExponent) (hN : Numbers ρ c x₀ lam B) (hj : j < l) (C₀ : ℕ) :
    levelBound ρ c x₀ C₀ l lam B j ≤
      (2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1) - 3 * ((K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / K x₀ j) *
        (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * (g x₀ j ^ 4 / 4) + K x₀ j ^ 2 + (c + 5) * C₀ * K x₀ j ^ 2) := by
  obtain ⟨hΛ, hBB⟩ := pos_of_chainLabel hL hN (by omega : j + 1 ≤ l)
  have hx1 : 1 ≤ x₀ := by have := hN.x₀_ge; omega
  have hXn := four_mul_le_xiAt hx1 ρ c l lam B j hBB
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (xiAt ρ c x₀ l lam B j : ℝ) := ⟨_, rfl⟩
  rw [← hX]
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℕ, Λ = lamAt ρ c x₀ l lam B (j + 1) := ⟨_, rfl⟩
  rw [← hΛd] at hΛ hXn
  have hX2 : 2 ≤ X := by rw [hX]; exact_mod_cast (by omega : 2 ≤ xiAt ρ c x₀ l lam B j)
  have hXΛ : 2 * (Λ : ℝ) ≤ X := by rw [hX]; exact_mod_cast (by omega : 2 * Λ ≤ xiAt ρ c x₀ l lam B j)
  have hΛ0 : (0 : ℝ) < 2 * (Λ : ℝ) := by have : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ
                                         linarith
  -- the polynomial factor
  have p1 : (baseAt ρ c x₀ l lam B j : ℝ) ≤ X ^ (c + 5) := by rw [hX]; exact_mod_cast hB ρ c x₀ l lam B j hN hj
  have p2 : (baseAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ j ^ 2) ≤ X ^ ((c + 5) * C₀ * K x₀ j ^ 2) := by
    calc (baseAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ j ^ 2) ≤ (X ^ (c + 5)) ^ (C₀ * K x₀ j ^ 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) p1 _
      _ = X ^ ((c + 5) * C₀ * K x₀ j ^ 2) := by rw [← pow_mul, Nat.mul_assoc]
  -- the power of 2
  have q0 := hE ρ c x₀ l lam B j hN hj
  rw [← hΛd] at q0 ⊢
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * Λ - 3 * ((K x₀ (j + 1) : ℝ) ^ 2 * Λ) / K x₀ j := ⟨_, rfl⟩
  rw [← hx]
  have eA : (c : ℝ) / 4 * (K x₀ (j + 1) : ℝ) ^ 2 = ((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) := by
    have h1 : ((4 * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) = ((K x₀ (j + 1) ^ 2 : ℕ) : ℝ) := by rw [four_mul_div_g hx1, K_succ_sq]
    push_cast at h1 ⊢
    rw [← h1]
    ring
  have q1 : e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j ≤ x + ((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) * Real.logb 2 (2 * Λ) + ((K x₀ j ^ 2 : ℕ) : ℝ) := by
    rw [← eA, hx]
    push_cast
    linarith
  have q2 : (2 : ℝ) ^ (((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) * Real.logb 2 (2 * Λ)) = (2 * (Λ : ℝ)) ^ (c * (g x₀ j ^ 4 / 4)) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hΛ0, Real.rpow_natCast]
  have q3 : (2 : ℝ) ^ (e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j) ≤ (2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4)) * X ^ (K x₀ j ^ 2) := by
    calc (2 : ℝ) ^ (e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j) ≤ (2 : ℝ) ^ (x + ((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) * Real.logb 2 (2 * Λ) + ((K x₀ j ^ 2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) q1
      _ = (2 : ℝ) ^ x * (2 * (Λ : ℝ)) ^ (c * (g x₀ j ^ 4 / 4)) * (2 : ℝ) ^ (K x₀ j ^ 2) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), q2, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4)) * X ^ (K x₀ j ^ 2) := by
          have hp : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
          exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΛ0.le hXΛ _) hp.le) (pow_le_pow_left₀ (by norm_num) hX2 _) (by positivity) (by positivity)
  unfold levelBound timeBound
  rw [baseAt_cast]
  calc (2 : ℝ) ^ (e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j) * (baseAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ j ^ 2)
      ≤ ((2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4)) * X ^ (K x₀ j ^ 2)) * X ^ ((c + 5) * C₀ * K x₀ j ^ 2) := mul_le_mul q3 p2 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4) + K x₀ j ^ 2 + (c + 5) * C₀ * K x₀ j ^ 2) := by rw [pow_add, pow_add]; ring
end ExplicitCost
