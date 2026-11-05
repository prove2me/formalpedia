-- Prove2me | solution 1 for ExplicitCost.partAPrinted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:24.365696+00:00
-- url     : https://prove2.me/submissions/9f7c3620-6fba-4fbb-b953-5ab569537a8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PartAPrinted
import Theorems.Thm_GeneralPieces_Chain_hoeffding_cond
import Theorems.Thm_GeneralPieces_PartA_e_ge_half_pow
import Theorems.Thm_GeneralPieces_PartA_e_le_of_y
import Theorems.Thm_GeneralPieces_PartA_logK_formula
import Theorems.Thm_GeneralPieces_PartA_rho_pow_le


set_option autoImplicit false
section
section
open ExplicitCost
namespace ExplicitCost
theorem _root_.solution : Levels.Gen.PartA where
  logK := GeneralPieces.PartA.logK_formula
  K_lt x₀ l hx := (GeneralPieces.PartA.K_lt_le x₀ l (by omega)).1
  K_le x₀ l hx := (GeneralPieces.PartA.K_lt_le x₀ l (by omega)).2
  e_ge ρ x₀ l hρ _ _ := by
    have := GeneralPieces.PartA.e_ge_half_pow ρ x₀ l hρ
    linarith
  e_le ρ x₀ l hρ _ hx := GeneralPieces.PartA.e_le_of_y ρ x₀ l hρ hx
  rho_pow ρ x₀ l hρ hρ1 hx := GeneralPieces.PartA.rho_pow_le ρ x₀ l (by linarith) hρ1.le (by omega)
  case_ii x₀ l hx := GeneralPieces.Chain.hoeffding_cond x₀ l hx
end ExplicitCost
