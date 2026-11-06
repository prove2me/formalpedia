-- Prove2me | solution 1 for ExplicitCost.readAsPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:43:22.976677+00:00
-- url     : https://prove2.me/submissions/c4b3e76b-9e7c-404d-a119-41c563595906

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Answers

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
variable {Q A A' α β : Type}
namespace ExplicitCost
theorem _root_.solution : ReadAsPoly := fun _ _ _ _ _ _ _ _ _ _ _ M hr ⟨_⟩ => ⟨readAsIsPolyQ hr M⟩
end ExplicitCost
