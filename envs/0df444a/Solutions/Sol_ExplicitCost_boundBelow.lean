-- Prove2me | solution 1 for ExplicitCost.boundBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:23:21.404597+00:00
-- url     : https://prove2.me/submissions/236172b4-ba87-408e-b533-04bab87fd4fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_boundBelowFrom
import Theorems.Thm_ExplicitCost_chainBase
import Theorems.Thm_ExplicitCost_chainExponent
import Theorems.Thm_ExplicitCost_chainLabel


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution : BoundBelow := boundBelowFrom chainLabel chainBase chainExponent
end ExplicitCost
