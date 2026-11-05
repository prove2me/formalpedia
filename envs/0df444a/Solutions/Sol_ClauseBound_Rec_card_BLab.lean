-- Prove2me | solution 1 for ClauseBound.Rec.card_BLab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:43:10.199827+00:00
-- url     : https://prove2.me/submissions/4984416d-3bd4-4cc7-80eb-a3333f3304fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_Blocks

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
variable {n h : ℕ}
namespace ClauseBound.Rec
theorem _root_.solution (b : Fin (nblk n h)) : Fintype.card (BLab n h b) = 4 ^ #(blk n h b.val) := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype]
  rfl
end ClauseBound.Rec
