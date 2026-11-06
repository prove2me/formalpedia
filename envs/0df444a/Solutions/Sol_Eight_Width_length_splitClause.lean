-- Prove2me | solution 1 for Eight.Width.length_splitClause
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:43.492198+00:00
-- url     : https://prove2.me/submissions/3c5a10eb-758e-485c-9449-c31558b9c27a

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
theorem _root_.solution : ∀ (ys : List V) (C : List (V × Bool)),
    (splitClause ys C).length = 1 + 3 * min ys.length (C.length - 3)
  | [], C => by rw [splitClause_nil]; simp
  | y :: ys, C => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC]; simp; omega
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, List.length_append, solution ys]
      simp [forced]; omega
end Eight.Width
