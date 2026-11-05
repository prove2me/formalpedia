-- Prove2me | solution 1 for Eight.forall_blockAt_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:39.48877+00:00
-- url     : https://prove2.me/submissions/3385d6e4-6f0e-4bf6-adcf-084ec398ec62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_bitAt_of_lt

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution {lam : ℕ} (x v : Pieces.Bits lam) : (∀ s ∈ range (tOf lam), blockAt x s = blockAt v s) ↔ x = v := by
  constructor
  · intro h
    funext j
    have hs : j.val / 3 ∈ range (tOf lam) := by
      have := j.isLt
      rw [mem_range]; unfold tOf; omega
    have hb := h _ hs
    simp only [blockAt, Prod.mk.injEq] at hb
    rw [← bitAt_of_lt x j, ← bitAt_of_lt v j]
    have h3 : j.val = 3 * (j.val / 3) ∨ j.val = 3 * (j.val / 3) + 1 ∨ j.val = 3 * (j.val / 3) + 2 := by omega
    rcases h3 with h3 | h3 | h3 <;> rw [h3]
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2
  · rintro rfl s _
    rfl
end Eight
