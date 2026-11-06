-- Prove2me | solution 1 for ExplicitCost.baseAt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:23.856141+00:00
-- url     : https://prove2.me/submissions/c7cfd2ee-91c4-4435-b057-a329e2cb3477

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution (ρ : ℝ) (c x₀ l lam B j : ℕ) : baseAt ρ c x₀ l lam B (j + 1) = xiAt ρ c x₀ l lam B j := rfl
end ExplicitCost
