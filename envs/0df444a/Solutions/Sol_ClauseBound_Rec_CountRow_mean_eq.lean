-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:56.900843+00:00
-- url     : https://prove2.me/submissions/6e0e62c8-6d86-44b4-8c0b-1a1a24ae790c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_share_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (n : ℕ) (hh : 1 ≤ h) :
    mean n h = ((∑ b ∈ range (nblk n h), (2 ^ #(blk n h b) - 1) * 2 ^ (h - #(blk n h b)) : ℕ) : ℝ) / ((2 ^ (h + 1) : ℕ) : ℝ) := by
  rw [Finset.sum_range, Nat.cast_sum, Finset.sum_div, mean]
  exact Finset.sum_congr rfl fun b _ => share_eq hh b
end ClauseBound.Rec.CountRow
