-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.card_blk_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:45:41.701902+00:00
-- url     : https://prove2.me/submissions/936be950-6915-4e77-87c0-80129d63efc3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_split_apply


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (hh : 1 ≤ h) (β : Lab n) (b : Fin (nblk n h)) :
    #{k ∈ blk n h b.val | β k = (true, true)} = #{k | split hh β b k = (true, true)} := by
  simp only [split_apply]
  have h1 : ({k : {k : Fin n // k.val / h = b.val} | β k.1 = (true, true)} : Finset _)
      = ({k : Fin n | β k = (true, true)} : Finset _).subtype fun k => k.val / h = b.val := by
    ext k; simp
  rw [h1, Finset.card_subtype, blk, Finset.filter_filter, Finset.filter_filter]
  congr 1
  ext k
  simp [and_comm]
end ClauseBound.Rec.CountRow
