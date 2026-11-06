-- Prove2me | solution 1 for Eight.Width.splitClause_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:32.164193+00:00
-- url     : https://prove2.me/submissions/50242fa0-7d91-4843-a260-7c6368843369

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_holds_append
import Theorems.Thm_Eight_Width_holds_forced
import Theorems.Thm_Eight_Width_splitClause_step
import Theorems.Thm_Eight_Width_exists_four

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution (b b' : V → Bool) : ∀ (ys : List V) (C : List (V × Bool)), ys.length ≤ C.length - 3 →
    (∀ l ∈ C, b l.1 = b' l.1) → Holds b (splitClause ys C) → Holds b' (splitClause ys C) → ∀ y ∈ ys, b y = b' y
  | [], _, _, _, _, _, y, hy => by simp at hy
  | y :: ys, C, hlen, hag, h, h', z, hz => by
    have hC : ¬ C.length ≤ 3 := by simp at hlen; omega
    obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
    rw [splitClause_step, holds_append, holds_forced] at h h'
    have hy : b y = b' y := by
      have e : (b y = true ↔ b' y = true) := by
        rw [h.1, h'.1, hag l₁ (by simp), hag l₂ (by simp)]
      cases hb : b y <;> cases hb' : b' y <;> simp_all
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hy
    · refine solution b b' ys _ (by simp at hlen ⊢; omega) ?_ h.2 h'.2 z hz
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hy
      · exact hag l (by simp only [List.mem_cons] at hl ⊢; tauto)
end Eight.Width
