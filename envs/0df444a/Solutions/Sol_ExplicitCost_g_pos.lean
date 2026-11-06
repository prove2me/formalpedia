-- Prove2me | solution 1 for ExplicitCost.g_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:16:45.683416+00:00
-- url     : https://prove2.me/submissions/25cec5fa-7ff9-4797-b677-7f1d7c8b660e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_K_le_g
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_ExplicitCost_K_pos
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution (x₀ j : ℕ) : 1 ≤ g x₀ j := (K_pos x₀ j).trans (K_le_g x₀ j)
end ExplicitCost
