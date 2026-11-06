-- Prove2me | solution 1 for ExplicitCost.recursion_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:11:57.234104+00:00
-- url     : https://prove2.me/submissions/e51236e2-39c7-4f27-9a25-91f66e7b4388

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyEnd
import Definitions.Def_ExplicitCost_GroupingPoly
import Definitions.Def_Tower_PolyTower
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyAll
import Theorems.Thm_ExplicitCost_recursionPoly
import Theorems.Thm_ExplicitCost_recursionPolyFrom
import Theorems.Thm_QueryMachines_Tower_towerPoly


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (c x₀ : ℕ) : (recursion c x₀).PolyTimeSteps := recursionPolyFrom Tower.towerPoly recursionPoly c x₀
end ExplicitCost
