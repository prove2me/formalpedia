-- Prove2me | solution 1 for Eight.Width.splitClause_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:09.819472+00:00
-- url     : https://prove2.me/submissions/3e5db27a-96c4-4b64-a889-cc237f94b621

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
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
theorem _root_.solution : ∀ (ys : List V) (C : List (V × Bool)), ∀ D ∈ splitClause ys C, ∀ l ∈ D,
    l.1 ∈ ys ∨ ∃ l' ∈ C, l'.1 = l.1
  | [], C, D, hD, l, hl => by
    rw [splitClause_nil] at hD
    obtain rfl : D = C := by simpa using hD
    exact Or.inr ⟨l, hl, rfl⟩
  | y :: ys, C, D, hD, l, hl => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC] at hD
      obtain rfl : D = C := by simpa using hD
      exact Or.inr ⟨l, hl, rfl⟩
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, List.mem_append] at hD
      rcases hD with hD | hD
      · simp only [forced, neg, List.mem_cons, List.not_mem_nil, or_false] at hD
        rcases hD with rfl | rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl | rfl <;> simp
      · rcases solution ys _ D hD l hl with h | ⟨l', hl', e⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.1 hl' with rfl | hl'
          · exact Or.inl (by simp [← e])
          · exact Or.inr ⟨l', by simp only [List.mem_cons] at hl' ⊢; tauto, e⟩
end Eight.Width
