-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.card_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:47:25.586083+00:00
-- url     : https://prove2.me/submissions/45fb0644-1815-48c7-9515-b72bc51990b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_card_lab

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (hh : 1 ≤ h) : Fintype.card (∀ b : Fin (nblk n h), BLab n h b) = 4 ^ n := by
  rw [← Fintype.card_congr (split hh), card_lab]
end ClauseBound.Rec.CountRow
