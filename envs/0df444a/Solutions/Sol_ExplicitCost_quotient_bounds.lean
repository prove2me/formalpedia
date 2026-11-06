-- Prove2me | solution 1 for ExplicitCost.quotient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:37.348202+00:00
-- url     : https://prove2.me/submissions/2e12c0a1-accc-47f5-8e39-09d5c8012f0b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution {r G4 Λ lg cc k2 : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hG : 0 ≤ G4) (hΛ : 0 ≤ Λ) (hlg0 : 0 ≤ lg) (hlg : lg ≤ Λ) (hc0 : 0 ≤ cc) (hk : 2 + cc / 4 ≤ k2) :
    1 ≤ (r * (G4 * Λ) + cc / 4 * G4 * lg + k2) / k2 ∧ (r * (G4 * Λ) + cc / 4 * G4 * lg + k2) / k2 ≤ G4 * Λ + 1 := by
  have hk0 : 0 < k2 := by linarith [div_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 4)]
  have hc4 : 0 ≤ cc / 4 := div_nonneg hc0 (by norm_num)
  have hGΛ : 0 ≤ G4 * Λ := mul_nonneg hG hΛ
  have a1 : 0 ≤ r * (G4 * Λ) := mul_nonneg hr0 hGΛ
  have a2 : 0 ≤ cc / 4 * G4 * lg := mul_nonneg (mul_nonneg hc4 hG) hlg0
  have a3 : r * (G4 * Λ) ≤ 2 * (G4 * Λ) := mul_le_mul_of_nonneg_right hr2 hGΛ
  have a4 : cc / 4 * G4 * lg ≤ cc / 4 * G4 * Λ := mul_le_mul_of_nonneg_left hlg (mul_nonneg hc4 hG)
  have a5 : (2 + cc / 4) * (G4 * Λ) ≤ k2 * (G4 * Λ) := mul_le_mul_of_nonneg_right hk hGΛ
  constructor
  · rw [le_div_iff₀ hk0]
    linarith
  · rw [div_le_iff₀ hk0]
    nlinarith
end ExplicitCost
