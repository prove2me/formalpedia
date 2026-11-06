-- Prove2me | solution 1 for ExplicitCost.const_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:44:36.571562+00:00
-- url     : https://prove2.me/submissions/fb33aa02-6a0b-4ac9-b5bd-5c76323c7a4a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]
namespace ExplicitCost
theorem _root_.solution [HasSize α] [HasSize β] [Carried α] [Carried β] (b : β) : (QueryMachine.const b : QueryMachine Q A α β).PolyTimeSteps := ⟨IsPolyQ.const b⟩
end ExplicitCost
