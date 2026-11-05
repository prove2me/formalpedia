-- Prove2me | solution 1 for Eight.Width.exists_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:30:54.480867+00:00
-- url     : https://prove2.me/submissions/8c059f98-99af-4091-bc9f-79c68afead9e

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
theorem _root_.solution {C : List (V × Bool)} (h : ¬ C.length ≤ 3) : ∃ l₁ l₂ l₃ l₄ r, C = l₁ :: l₂ :: l₃ :: l₄ :: r := by
  match C, h with
  | l₁ :: l₂ :: l₃ :: l₄ :: r, _ => exact ⟨l₁, l₂, l₃, l₄, r, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h => simp at h
end Eight.Width
