-- Prove2me | solution 1 for ExplicitCost.K_le_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:06:37.071226+00:00
-- url     : https://prove2.me/submissions/e5a92ccb-f074-4fd7-9bf5-588cb259e21b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution (x₀ j : ℕ) : K x₀ j ≤ g x₀ j := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))
end ExplicitCost
