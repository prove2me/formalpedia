-- Prove2me | solution 1 for Eight.bxor_right_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:48:35.480213+00:00
-- url     : https://prove2.me/submissions/6cf76e32-57fa-464f-a82c-741edac97d0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {x v y : Block} (h : bxor x y = bxor v y) : x = v := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y; obtain ⟨v1, v2, v3⟩ := v
  have hb : ∀ a b c : Bool, (a ^^ b) = (c ^^ b) → a = c := by decide
  simp only [bxor, Prod.mk.injEq] at h ⊢
  exact ⟨hb _ _ _ h.1, hb _ _ _ h.2.1, hb _ _ _ h.2.2⟩
end Eight
