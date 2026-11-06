-- Prove2me | solution 1 for Eight.Width.splitClause_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:01:24.253239+00:00
-- url     : https://prove2.me/submissions/efce7fa5-7c7f-4fdd-b661-18bd355d5017

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_stForced
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
theorem _root_.solution : ∀ (ys : List V) (C : List (V × Bool)), C.length - 3 ≤ ys.length →
    ∀ D ∈ splitClause ys C, D.length ≤ 3
  | [], C, h, D, hD => by
    rw [splitClause_nil] at hD
    obtain rfl : D = C := by simpa using hD
    simp at h; omega
  | y :: ys, C, h, D, hD => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC] at hD
      obtain rfl : D = C := by simpa using hD
      exact hC
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, List.mem_append] at hD
      rcases hD with hD | hD
      · exact (stForced V (fun _ => true) y l₁ l₂).2 D hD
      · exact solution ys _ (by simp at h ⊢; omega) D hD
end Eight.Width
