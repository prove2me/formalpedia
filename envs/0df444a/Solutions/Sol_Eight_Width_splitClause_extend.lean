-- Prove2me | solution 1 for Eight.Width.splitClause_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:31.076563+00:00
-- url     : https://prove2.me/submissions/c7194c0f-28d9-49e0-9321-779947ed3444

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
theorem _root_.solution : ∀ (ys : List V) (C : List (V × Bool)) (a : V → Bool), ys.Nodup → (∀ l ∈ C, l.1 ∉ ys) →
    (∃ l ∈ C, a l.1 = l.2) → ∃ b : V → Bool, (∀ v, v ∉ ys → b v = a v) ∧ Holds b (splitClause ys C)
  | [], C, a, _, _, h => ⟨a, fun _ _ => rfl, by rw [splitClause_nil]; simpa [Holds] using h⟩
  | y :: ys, C, a, hn, hf, h => by
    classical
    by_cases hC : C.length ≤ 3
    · exact ⟨a, fun _ _ => rfl, by rw [splitClause_short _ hC]; simpa [Holds] using h⟩
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      obtain ⟨hy, hn⟩ := List.nodup_cons.1 hn
      have hne : ∀ l ∈ l₁ :: l₂ :: l₃ :: l₄ :: r, l.1 ≠ y := fun l hl e => hf l hl (by simp [e])
      have hnm : ∀ l ∈ l₁ :: l₂ :: l₃ :: l₄ :: r, l.1 ∉ ys := fun l hl e => hf l hl (List.mem_cons_of_mem _ e)
      let a' : V → Bool := Function.update a y (decide (a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2))
      have ha' : ∀ l ∈ l₁ :: l₂ :: l₃ :: l₄ :: r, a' l.1 = a l.1 := fun l hl => Function.update_of_ne (hne l hl) _ _
      have hay : a' y = decide (a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2) := Function.update_self _ _ _
      obtain ⟨b, hb, hH⟩ := solution ys ((y, true) :: l₃ :: l₄ :: r) a' hn
        (by
          intro l hl
          rcases List.mem_cons.1 hl with rfl | hl
          · exact hy
          · exact hnm l (by simp only [List.mem_cons] at hl ⊢; tauto))
        (by
          obtain ⟨l, hl, e⟩ := h
          by_cases h12 : a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2
          · exact ⟨(y, true), by simp, by simp [hay, h12]⟩
          · have hl' : l ∈ l₃ :: l₄ :: r := by
              simp only [List.mem_cons] at hl ⊢
              rcases hl with rfl | rfl | hl
              · exact absurd (Or.inl e) h12
              · exact absurd (Or.inr e) h12
              · exact hl
            exact ⟨l, List.mem_cons_of_mem _ hl', by rw [ha' l hl]; exact e⟩)
      refine ⟨b, fun v hv => ?_, ?_⟩
      · rw [hb v fun h => hv (List.mem_cons_of_mem _ h)]
        exact Function.update_of_ne (fun e => hv (by simp [e])) _ _
      · rw [splitClause_step, holds_append, holds_forced]
        refine ⟨?_, hH⟩
        rw [hb y hy, hb _ (hnm l₁ (by simp)), hb _ (hnm l₂ (by simp)), ha' l₁ (by simp), ha' l₂ (by simp), hay]
        simp
end Eight.Width
