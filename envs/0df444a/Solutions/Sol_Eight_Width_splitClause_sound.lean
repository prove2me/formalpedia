-- Prove2me | solution 1 for Eight.Width.splitClause_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:08.834418+00:00
-- url     : https://prove2.me/submissions/0d62a2e8-69d5-44df-be4c-93f7b3ae6bee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_holds_append
import Theorems.Thm_Eight_Width_holds_forced
import Theorems.Thm_Eight_Width_splitClause_step
import Theorems.Thm_Eight_Width_splitClause_nil
import Theorems.Thm_Eight_Width_splitClause_short
import Theorems.Thm_Eight_Width_exists_four

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution (a : V → Bool) : ∀ (ys : List V) (C : List (V × Bool)),
    Holds a (splitClause ys C) → ∃ l ∈ C, a l.1 = l.2
  | [], C, h => by
    rw [splitClause_nil] at h
    exact h C (by simp)
  | y :: ys, C, h => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC] at h
      exact h C (by simp)
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, holds_append, holds_forced] at h
      obtain ⟨l, hl, e⟩ := solution a ys _ h.2
      rcases List.mem_cons.1 hl with rfl | hl
      · rcases h.1.1 e with e | e
        · exact ⟨l₁, by simp, e⟩
        · exact ⟨l₂, by simp, e⟩
      · exact ⟨l, by simp only [List.mem_cons] at hl ⊢; tauto, e⟩
end Eight.Width
