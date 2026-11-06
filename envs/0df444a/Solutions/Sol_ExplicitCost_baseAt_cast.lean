-- Prove2me | solution 1 for ExplicitCost.baseAt_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:19:23.183113+00:00
-- url     : https://prove2.me/submissions/3cf39312-6a0f-46fe-ab3b-ec609e54b893

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (ρ : ℝ) (c x₀ l lam B j : ℕ) : (K x₀ j : ℝ) * ((lamAt ρ c x₀ l lam B j : ℝ) + bitsAt ρ c x₀ l lam B j) = (baseAt ρ c x₀ l lam B j : ℝ) := by
  unfold baseAt
  push_cast
  ring
end ExplicitCost
