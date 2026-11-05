-- Prove2me | solution 1 for Eight.Width.holds_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:15.29077+00:00
-- url     : https://prove2.me/submissions/b33c893c-267f-4ba5-8422-b39d21b98823

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
theorem _root_.solution {a : V → Bool} {C : List (V × Bool)} {φ : List (List (V × Bool))} :
    Holds a (C :: φ) ↔ (∃ l ∈ C, a l.1 = l.2) ∧ Holds a φ := by simp [Holds]
end Eight.Width
