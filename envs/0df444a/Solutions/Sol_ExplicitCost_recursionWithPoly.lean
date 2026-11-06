-- Prove2me | solution 1 for ExplicitCost.recursionWithPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:17:05.144208+00:00
-- url     : https://prove2.me/submissions/82866a3b-062b-4b75-86b5-291b52921641

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyEnd
import Definitions.Def_ExplicitCost_GroupingPoly
import Definitions.Def_Tower_PolyTower
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyAll
import Theorems.Thm_ExplicitCost_recursion_poly
import Theorems.Thm_ExplicitCost_recursionWithPolyFrom


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : RecursionWithPoly := recursionWithPolyFrom recursion_poly
end ExplicitCost
