-- Prove2me | solution 1 for Eight.Width.splitAll_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:04:42.234091+00:00
-- url     : https://prove2.me/submissions/132e6451-d671-4347-87eb-ede2007e5937

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_splitClause_width
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
    ∀ D ∈ splitAll ys φ, D.length ≤ 3
  | [], _, _, D, hD => by simp [splitAll] at hD
  | C :: φ, ys, hlen, D, hD => by
    rw [numFresh_cons] at hlen
    rw [splitAll_cons, List.mem_append] at hD
    rcases hD with hD | hD
    · exact splitClause_width _ C (by simp; omega) D hD
    · exact solution φ _ (by simp; omega) D hD
end Eight.Width
