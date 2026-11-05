-- Prove2me | solution 1 for Eight.natDegree_prod_linear_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:14.314527+00:00
-- url     : https://prove2.me/submissions/49a12c65-f9d5-4c04-a7f7-872139ce330d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution (S : Finset ℕ) (r c : ℕ → ℤ) : (∏ s ∈ S, (C (r s) + X * C (c s))).natDegree ≤ #S := by
  refine (natDegree_prod_le S _).trans ?_
  have h : ∀ s ∈ S, (C (r s) + X * C (c s)).natDegree ≤ 1 := fun s _ => by compute_degree
  simpa using sum_le_card_nsmul S _ 1 h
end Eight
