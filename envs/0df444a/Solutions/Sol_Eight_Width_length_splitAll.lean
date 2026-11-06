-- Prove2me | solution 1 for Eight.Width.length_splitAll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:00.093033+00:00
-- url     : https://prove2.me/submissions/43b8ff66-e150-450d-87f9-a35d99d37afe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_length_splitClause
import Theorems.Thm_Eight_Width_splitAll_cons
import Theorems.Thm_Eight_Width_numFresh_cons

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution : ∀ (φ : List (List (V × Bool))) (ys : List V), numFresh φ ≤ ys.length →
    (splitAll ys φ).length = φ.length + 3 * numFresh φ
  | [], _, _ => by simp [splitAll, numFresh]
  | C :: φ, ys, hlen => by
    rw [numFresh_cons] at hlen
    rw [splitAll_cons, List.length_append, length_splitClause, solution φ _ (by simp; omega), numFresh_cons]
    simp; omega
end Eight.Width
