-- Prove2me | solution 1 for ExplicitCost.levelBound_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:32.219932+00:00
-- url     : https://prove2.me/submissions/5550feb4-59b2-4e4e-9f8b-3267c12773fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_levelBound_le_succ
import Theorems.Thm_ExplicitCost_bitsAt_self
import Theorems.Thm_ExplicitCost_lamAt_self
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hL : ChainLabel) (hBl : BoundBelow) (hEF : ExponentFits) (hN : Numbers ρ c x₀ lam B) {C₀ : ℕ} (hC : 2 * (c + 1) ≤ C₀) (l : ℕ) :
    ∀ k j, j + k = l → levelBound ρ c x₀ C₀ l lam B j ≤ timeBound ρ x₀ C₀ l lam B := by
  intro k
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = l := by omega
    unfold levelBound
    rw [lamAt_self, bitsAt_self]
  | succ k ih =>
    intro j hj
    exact (levelBound_le_succ hL hBl hEF hN (by omega) hC).trans (ih (j + 1) (by omega))
end ExplicitCost
