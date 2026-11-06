-- Prove2me | solution 1 for Eight.Width.splitAll_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:18.62821+00:00
-- url     : https://prove2.me/submissions/70b5c2d1-c776-440d-b749-91ca9434c0ac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_holds_append
import Theorems.Thm_Eight_Width_splitClause_unique
import Theorems.Thm_Eight_Width_splitAll_cons
import Theorems.Thm_Eight_Width_numFresh_cons

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution (b b' : V → Bool) : ∀ (φ : List (List (V × Bool))) (ys : List V), ys.length ≤ numFresh φ →
    (∀ C ∈ φ, ∀ l ∈ C, b l.1 = b' l.1) → Holds b (splitAll ys φ) → Holds b' (splitAll ys φ) → ∀ y ∈ ys, b y = b' y
  | [], ys, hlen, _, _, _, y, hy => by
    obtain rfl : ys = [] := List.length_eq_zero_iff.1 (by simpa [numFresh] using hlen)
    simp at hy
  | C :: φ, ys, hlen, hag, h, h', y, hy => by
    rw [splitAll_cons, holds_append] at h h'
    rw [numFresh_cons] at hlen
    rw [← List.take_append_drop (C.length - 3) ys, List.mem_append] at hy
    rcases hy with hy | hy
    · exact splitClause_unique b b' _ C (by simp) (hag C (by simp)) h.1 h'.1 y hy
    · exact solution b b' φ _ (by simp; omega) (fun D hD => hag D (List.mem_cons_of_mem _ hD)) h.2 h'.2 y hy
end Eight.Width
