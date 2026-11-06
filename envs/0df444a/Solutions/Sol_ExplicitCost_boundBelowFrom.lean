-- Prove2me | solution 1 for ExplicitCost.boundBelowFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:09:34.206283+00:00
-- url     : https://prove2.me/submissions/f6a74b36-4a3a-4385-8566-475af111c441

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_level_le

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution : BoundBelowFrom := fun hL hB hE _ _ _ C₀ _ _ _ _ hN hj => level_le hL hB hE hN hj C₀
end ExplicitCost
