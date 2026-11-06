-- Prove2me | solution 1 for ExplicitCost.chainExponentFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:26:25.370727+00:00
-- url     : https://prove2.me/submissions/1ef38bb7-1a06-4f06-9dd7-2bad8a319a33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain
import Theorems.Thm_ExplicitCost_exponent_real
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_Eight_Level_rho_ge
import Theorems.Thm_ExplicitCost_K_pos
import Theorems.Thm_ExplicitCost_K_succ_sq
import Theorems.Thm_ExplicitCost_one_le_lamAt
import Theorems.Thm_GeneralPieces_DefGenPieces_logb_nonneg


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution : ChainExponentFrom := by
  intro hL hA ρ c x₀ l lam B j hN hj
  obtain ⟨-, -, -, h4⟩ := hL ρ c x₀ l lam B j hN hj
  have he0 : 0 ≤ e ρ x₀ j := le_trans (by have := hN.rho_ge; positivity) (hA.e_ge ρ x₀ j hN.rho_ge hN.rho_lt hN.x₀_ge)
  have he1 : e ρ x₀ j ≤ 1 := by
    have h1 := hA.e_le ρ x₀ j hN.rho_ge hN.rho_lt hN.x₀_ge
    have h2 : ρ ^ j ≤ 1 := pow_le_one₀ (by linarith [hN.rho_ge]) hN.rho_lt.le
    linarith
  have hK : (0 : ℝ) < K x₀ j := by exact_mod_cast K_pos x₀ j
  have hlg := GeneralPieces.DefGenPieces.logb_nonneg (one_le_lamAt hN (by omega : j + 1 ≤ l))
  have eK : (K x₀ (j + 1) : ℝ) ^ 2 = (g x₀ j : ℝ) ^ 4 := by exact_mod_cast K_succ_sq x₀ j
  have h := exponent_real (kk := K x₀ j) he0 he1 hK (by positivity) (by positivity) h4
  rw [eK]
  have ee : e ρ x₀ (j + 1) = (ρ + 3 * zeta j) * e ρ x₀ j + 3 / K x₀ j := rfl
  rw [ee]
  linarith
end ExplicitCost
