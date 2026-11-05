-- Prove2me | solution 1 for Eight.prod_cross_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:52:32.732001+00:00
-- url     : https://prove2.me/submissions/5ba08d86-3685-4208-919a-d119ab3b3b75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_forall_blockAt_eq_iff

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution {lam : ℕ} (x y u v : Pieces.Bits lam) :
    ∏ s ∈ range (tOf lam), (if blockAt x s = blockAt v s ∧ blockAt y s = blockAt u s then (1 : ℤ) else 0) = Pieces.cross x y u v := by
  rw [prod_ite_zero, prod_const_one, Pieces.cross]
  refine if_congr ?_ rfl rfl
  rw [← forall_blockAt_eq_iff x v, ← forall_blockAt_eq_iff y u]
  exact ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩, fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩
end Eight
