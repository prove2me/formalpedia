-- Prove2me | solution 1 for ExplicitCost.readAs_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:01:01.245007+00:00
-- url     : https://prove2.me/submissions/469a7cc3-87d4-4a92-87cc-7f1ae97b5375

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules
import Theorems.Thm_ExplicitCost_readAsPoly


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]
namespace ExplicitCost
theorem _root_.solution {r : A' → A} (hr : PolyT r) {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) : (readAs r M).PolyTimeSteps := readAsPoly _ _ _ _ _ r M hr hM
end ExplicitCost
