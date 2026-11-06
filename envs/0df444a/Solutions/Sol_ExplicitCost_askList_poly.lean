-- Prove2me | solution 1 for ExplicitCost.askList_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:22:38.673699+00:00
-- url     : https://prove2.me/submissions/e375659c-6907-4e4d-9e40-6279dd794c3b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules
import Theorems.Thm_ExplicitCost_query_poly
import Theorems.Thm_ExplicitCost_mapOut_poly
import Theorems.Thm_ExplicitCost_asList_polyT

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]
namespace ExplicitCost
theorem _root_.solution [HasSize α] [Carried α] {h : α → Q} (hh : PolyT h) : (askList h).PolyTimeSteps := mapOut_poly (query_poly hh) asList_polyT
end ExplicitCost
