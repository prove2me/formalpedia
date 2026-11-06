-- Prove2me | solution 1 for ExplicitCost.recursionWithPolyFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:51:02.865575+00:00
-- url     : https://prove2.me/submissions/4b223a98-879b-4134-adb8-a664e8121a92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_PolyProcedure
import Definitions.Def_CountedRecursion_PolySolver
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyEnd
import Theorems.Thm_ExplicitCost_recursionWithPoly_of

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : RecursionWithPolyFrom := recursionWithPoly_of
end ExplicitCost
