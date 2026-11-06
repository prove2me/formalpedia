-- Prove2me | solution 1 for ExplicitCost.branch_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:20.626131+00:00
-- url     : https://prove2.me/submissions/281f28bd-3527-423d-9bcd-078b98273bbb

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
theorem _root_.solution {sel : α → α₁ ⊕ α₂} (hs : PolyT sel) {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} (h₁ : M₁.PolyTimeSteps) (h₂ : M₂.PolyTimeSteps) :
    (QueryMachine.branch sel M₁ M₂).PolyTimeSteps := by
  obtain ⟨_⟩ := h₁
  obtain ⟨_⟩ := h₂
  exact ⟨IsPolyQ.branch M₁ M₂ hs⟩
end ExplicitCost
