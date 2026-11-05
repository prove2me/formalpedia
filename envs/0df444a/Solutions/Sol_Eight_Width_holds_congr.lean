-- Prove2me | solution 1 for Eight.Width.holds_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:41.860512+00:00
-- url     : https://prove2.me/submissions/452f3a78-3664-4fdc-970d-d7bccf365349

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
theorem _root_.solution {a b : V → Bool} {φ : List (List (V × Bool))} (h : ∀ C ∈ φ, ∀ l ∈ C, a l.1 = b l.1) :
    Holds a φ ↔ Holds b φ := by
  constructor
  · intro ha C hC
    obtain ⟨l, hl, e⟩ := ha C hC
    exact ⟨l, hl, by rw [← h C hC l hl]; exact e⟩
  · intro hb C hC
    obtain ⟨l, hl, e⟩ := hb C hC
    exact ⟨l, hl, by rw [h C hC l hl]; exact e⟩
end Eight.Width
