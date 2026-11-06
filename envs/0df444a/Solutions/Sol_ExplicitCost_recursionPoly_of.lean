-- Prove2me | solution 1 for ExplicitCost.recursionPoly_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:00:33.097605+00:00
-- url     : https://prove2.me/submissions/efa0ab53-8a41-44c3-8f4a-3ceb4b01826f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_PolyProcedure
import Definitions.Def_CountedRecursion_PolySolver
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyEnd
import Theorems.Thm_ExplicitCost_procedure_poly
import Theorems.Thm_ExplicitCost_solver_poly


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hG : groupingCall.PolyTimeSteps) : RecursionPoly := fun c x₀ => ⟨solver_poly hG c x₀, procedure_poly c⟩
end ExplicitCost
