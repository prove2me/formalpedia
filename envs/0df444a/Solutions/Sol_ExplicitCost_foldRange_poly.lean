-- Prove2me | solution 1 for ExplicitCost.foldRange_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:56.868405+00:00
-- url     : https://prove2.me/submissions/dcd0027c-5539-4a1e-8704-574098731b48

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
theorem _root_.solution [HasSize α] [Carried α] [HasSize γ] [Carried γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} (hN : PolyT N) (hM : M.PolyTimeSteps)
    (hg : PolyT fun p : γ × ℕ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) : (QueryMachine.foldRange N M g c₀).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.foldRange M hN hg hc⟩
end ExplicitCost
