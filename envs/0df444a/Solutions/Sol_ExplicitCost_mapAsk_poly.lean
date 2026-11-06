-- Prove2me | solution 1 for ExplicitCost.mapAsk_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:59:04.792912+00:00
-- url     : https://prove2.me/submissions/7a607834-4ee0-43dd-b197-5aa203e2da1a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]
namespace ExplicitCost
theorem _root_.solution {h : Q → Q'} (hh : PolyT h) {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) : (QueryMachine.mapAsk h M).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.mapAsk hh M⟩
end ExplicitCost
