-- Prove2me | solution 1 for Eight.Width.holds_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:37.901194+00:00
-- url     : https://prove2.me/submissions/07c2ec57-74aa-4c31-a131-e6c5455ed231

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution (a : V → Bool) (y : V) (l₁ l₂ : V × Bool) :
    Holds a (forced y l₁ l₂) ↔ (a y = true ↔ a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2) := by
  obtain ⟨v₁, s₁⟩ := l₁
  obtain ⟨v₂, s₂⟩ := l₂
  simp only [Holds, forced, neg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp,
    exists_eq_left]
  generalize a y = p
  generalize a v₁ = q₁
  generalize a v₂ = q₂
  cases p <;> cases q₁ <;> cases q₂ <;> cases s₁ <;> cases s₂ <;> simp
end Eight.Width
