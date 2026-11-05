-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.two_mul_card_odd_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:49:59.134235+00:00
-- url     : https://prove2.me/submissions/beb7960e-7444-4c3b-bf90-40ba6ce9a6d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_two_mul_card_odd_add

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] :
    2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} ≤ Fintype.card (ι → Bool × Bool) :=
  (Nat.le_add_right _ _).trans (two_mul_card_odd_add ι).le
end ClauseBound.Rec.CountRow
