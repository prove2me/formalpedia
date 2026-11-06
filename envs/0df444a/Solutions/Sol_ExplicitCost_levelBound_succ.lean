-- Prove2me | solution 1 for ExplicitCost.levelBound_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:26:07.3792+00:00
-- url     : https://prove2.me/submissions/0707e449-0a13-44d5-86d5-571bb9ec348e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_baseAt_cast
import Theorems.Thm_ExplicitCost_baseAt_succ


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (ρ : ℝ) (c x₀ C₀ l lam B j : ℕ) : levelBound ρ c x₀ C₀ l lam B (j + 1) =
    (2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) * (xiAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ (j + 1) ^ 2) := by
  unfold levelBound timeBound
  rw [baseAt_cast, baseAt_succ]
end ExplicitCost
