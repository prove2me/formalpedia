-- Prove2me | solution 1 for ExplicitCost.two_add_le_K_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:41:23.432189+00:00
-- url     : https://prove2.me/submissions/ee866451-f363-4060-994a-eb037cdf073d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
import Theorems.Thm_ExplicitCost_two_pow_le_K
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hc : c + 5 ≤ 2 ^ x₀) (j : ℕ) : 2 + (c : ℝ) / 4 ≤ (K x₀ j : ℝ) ^ 2 := by
  have h1 : c + 5 ≤ K x₀ j := hc.trans (two_pow_le_K x₀ j)
  have h2 : ((c : ℝ) + 5) ≤ K x₀ j := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  nlinarith
end ExplicitCost
