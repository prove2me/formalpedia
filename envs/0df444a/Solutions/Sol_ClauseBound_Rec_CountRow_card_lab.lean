-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.card_lab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:45:56.829583+00:00
-- url     : https://prove2.me/submissions/0b7582f7-d735-49b2-9cd7-33e23e97246e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (n : ℕ) : Fintype.card (Lab n) = 4 ^ n := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
end ClauseBound.Rec.CountRow
