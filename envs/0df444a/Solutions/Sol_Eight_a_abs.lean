-- Prove2me | solution 1 for Eight.a_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:17.367946+00:00
-- url     : https://prove2.me/submissions/241c5698-ec34-412f-96da-a6090698e8f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_abs_A_le_choose

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam := by
  intro lam i _ _ x y u v
  refine (abs_A_le_choose lam i x y u v).trans ?_
  exact_mod_cast Nat.choose_le_two_pow (tOf lam) i
end Eight
