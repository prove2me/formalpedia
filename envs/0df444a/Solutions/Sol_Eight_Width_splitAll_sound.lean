-- Prove2me | solution 1 for Eight.Width.splitAll_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:01:57.760702+00:00
-- url     : https://prove2.me/submissions/9b217c51-8d8f-428a-84a5-0938cff3e803

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_holds_nil
import Theorems.Thm_Eight_Width_holds_cons
import Theorems.Thm_Eight_Width_holds_append
import Theorems.Thm_Eight_Width_splitClause_sound
import Theorems.Thm_Eight_Width_splitAll_cons

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution (a : V → Bool) : ∀ (φ : List (List (V × Bool))) (ys : List V), Holds a (splitAll ys φ) → Holds a φ
  | [], _, _ => holds_nil a
  | C :: φ, ys, h => by
    rw [splitAll_cons, holds_append] at h
    exact holds_cons.2 ⟨splitClause_sound a _ C h.1, solution a φ _ h.2⟩
end Eight.Width
