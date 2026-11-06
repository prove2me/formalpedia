-- Prove2me | solution 1 for ExplicitCost.bind_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:09:19.519106+00:00
-- url     : https://prove2.me/submissions/f9c8f6dd-87ad-4ac6-a0d2-b82f0a46627c

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
theorem _root_.solution [HasSize α] [Carried α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (QueryMachine.bind M N).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  obtain ⟨_⟩ := hN
  exact ⟨IsPolyQ.bind M N⟩
end ExplicitCost
