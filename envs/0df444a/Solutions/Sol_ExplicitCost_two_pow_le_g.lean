-- Prove2me | solution 1 for ExplicitCost.two_pow_le_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:41:11.437206+00:00
-- url     : https://prove2.me/submissions/085e6075-7322-492a-899e-5fe4210ae10f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_two_pow_le_K
import Theorems.Thm_ExplicitCost_K_le_g
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution (x₀ j : ℕ) : 2 ^ x₀ ≤ g x₀ j := (two_pow_le_K x₀ j).trans (K_le_g x₀ j)
end ExplicitCost
