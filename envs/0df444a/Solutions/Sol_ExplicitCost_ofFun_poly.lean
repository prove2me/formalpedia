-- Prove2me | solution 1 for ExplicitCost.ofFun_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:59:03.336665+00:00
-- url     : https://prove2.me/submissions/f6e31b36-8c43-487c-bf9c-39129687a53b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules
import Theorems.Thm_ExplicitCost_lift_poly

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]
namespace ExplicitCost
theorem _root_.solution [HasSize α] [HasSize β] [Carried α] [Carried β] {f : α → β} (hf : PolyT f) : (QueryMachine.lift (Stepped.ofFun f) : QueryMachine Q A α β).PolyTimeSteps :=
  lift_poly ⟨IsPolyT.ofFun hf⟩
end ExplicitCost
