-- Prove2me | solution 1 for ExplicitCost.mapIn_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:40:32.540052+00:00
-- url     : https://prove2.me/submissions/1c0bd529-9fa0-4b9f-b2b0-50a3da659236

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
theorem _root_.solution {g : α → β} (hg : PolyT g) {M : QueryMachine Q A β γ} (hM : M.PolyTimeSteps) : (QueryMachine.mapIn g M).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.mapIn hg M⟩
end ExplicitCost
