-- Prove2me | solution 1 for ClauseBound.Rec.nblk_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:52.456864+00:00
-- url     : https://prove2.me/submissions/e5c160cc-37b9-4b99-85bb-9e4315876cad

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
theorem _root_.solution (n : ℕ) (hh : 1 ≤ h) : nblk n h ≤ n := by
  unfold nblk
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have : n ≤ h * n := Nat.le_mul_of_pos_left n hh
  omega
end ClauseBound.Rec
