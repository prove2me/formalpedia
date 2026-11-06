-- Prove2me | solution 1 for ExplicitCost.K_succ_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:23:26.187709+00:00
-- url     : https://prove2.me/submissions/6d446d57-ac63-4240-b88d-fbf8b845035c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_K_succ_eq

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution (x₀ j : ℕ) : K x₀ (j + 1) ^ 2 = g x₀ j ^ 4 := by rw [K_succ_eq, ← pow_mul]
end ExplicitCost
