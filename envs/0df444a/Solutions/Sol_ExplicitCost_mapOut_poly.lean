-- Prove2me | solution 1 for ExplicitCost.mapOut_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:41:31.232196+00:00
-- url     : https://prove2.me/submissions/cb0fce6d-0f55-48a4-9840-feb893c13722

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
theorem _root_.solution {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) {g : β → γ} (hg : PolyT g) : (QueryMachine.mapOut M g).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.mapOut M hg⟩
end ExplicitCost
