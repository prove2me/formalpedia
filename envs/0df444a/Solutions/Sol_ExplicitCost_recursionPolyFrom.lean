-- Prove2me | solution 1 for ExplicitCost.recursionPolyFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:01:04.974587+00:00
-- url     : https://prove2.me/submissions/7cea391a-6a12-4127-b158-e40278afb428

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_PolyProcedure
import Definitions.Def_CountedRecursion_PolySolver
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyEnd

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : RecursionPolyFrom := fun hT hR c x₀ => hT _ _ _ _ _ _ (hR c x₀).1 (hR c x₀).2
end ExplicitCost
