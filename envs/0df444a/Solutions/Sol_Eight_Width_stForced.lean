-- Prove2me | solution 1 for Eight.Width.stForced
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:21:44.989218+00:00
-- url     : https://prove2.me/submissions/eacace9d-f5a3-484a-8c8b-eea8cabb347f

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

theorem solution : StForced := by
  intro V a y l₁ l₂
  rcases l₁ with ⟨x₁, b₁⟩
  rcases l₂ with ⟨x₂, b₂⟩
  cases h₁ : a x₁ <;> cases h₂ : a x₂ <;> cases b₁ <;> cases b₂ <;>
    cases hy : a y <;> simp [Holds, forced, neg, h₁, h₂, hy] <;> aesop
