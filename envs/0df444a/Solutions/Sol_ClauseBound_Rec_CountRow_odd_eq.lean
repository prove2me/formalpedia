-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.odd_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:47:28.090812+00:00
-- url     : https://prove2.me/submissions/8ce954f3-7568-403e-8631-d1083c4b242b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_card_blk_filter

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (hh : 1 ≤ h) (β : Lab n) : odd h β = #{b | split hh β b ∈ oddSet n h b} := by
  unfold odd oddSet
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mem_filter, mem_univ, true_and, card_blk_filter hh]
end ClauseBound.Rec.CountRow
