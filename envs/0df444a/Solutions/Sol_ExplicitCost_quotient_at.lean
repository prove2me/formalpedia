-- Prove2me | solution 1 for ExplicitCost.quotient_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:52:01.483201+00:00
-- url     : https://prove2.me/submissions/54b520df-1c10-42d1-a5bd-4cfcdb5e2d69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
import Theorems.Thm_ExplicitCost_zeta_bounds
import Theorems.Thm_ExplicitCost_quotient_bounds
import Theorems.Thm_ExplicitCost_two_add_le_K_sq
import Theorems.Thm_Eight_Level_rho_ge
import Theorems.Thm_GeneralPieces_DefGenPieces_logb_le
import Theorems.Thm_GeneralPieces_DefGenPieces_logb_nonneg


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hN : Numbers ρ c x₀ lam B) (j : ℕ) {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    1 ≤ ((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * Λ) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * Λ) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2 ∧
    ((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * Λ) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * Λ) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2 ≤ (g x₀ j : ℝ) ^ 4 * Λ + 1 :=
  quotient_bounds (by linarith [hN.rho_ge, (zeta_bounds j).1]) (by linarith [hN.rho_lt, (zeta_bounds j).2]) (by positivity) (Nat.cast_nonneg _) (GeneralPieces.DefGenPieces.logb_nonneg hΛ) (GeneralPieces.DefGenPieces.logb_le hΛ)
    (Nat.cast_nonneg _) (two_add_le_K_sq hN.x₀_c j)
end ExplicitCost
