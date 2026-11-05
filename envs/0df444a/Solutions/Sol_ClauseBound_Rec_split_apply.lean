-- Prove2me | solution 1 for ClauseBound.Rec.split_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:43:09.178858+00:00
-- url     : https://prove2.me/submissions/9e767d63-4257-44b0-8928-7e13fdcc2d45

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
theorem _root_.solution (hh : 1 ≤ h) (β : Lab n) (b : Fin (nblk n h)) (k : {k : Fin n // k.val / h = b.val}) :
    split hh β b k = β k.1 := by
  unfold split
  rfl
end ClauseBound.Rec
