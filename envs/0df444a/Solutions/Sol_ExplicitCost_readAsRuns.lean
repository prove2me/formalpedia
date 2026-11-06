-- Prove2me | solution 1 for ExplicitCost.readAsRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:43:21.539228+00:00
-- url     : https://prove2.me/submissions/3566e93d-720a-4711-8aca-91d1928a850a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Answers
import Theorems.Thm_ExplicitCost_readAs_reaches

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
variable {Q A A' α β : Type}
namespace ExplicitCost
theorem _root_.solution : ReadAsRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hr => readAs_reaches h hr
end ExplicitCost
