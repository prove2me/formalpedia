-- Prove2me | solution 1 for ClauseBound.Grid.card_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:47.61813+00:00
-- url     : https://prove2.me/submissions/3d0120c0-3c0c-4144-b424-7d7011f40543

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution {d : ℕ} (X : Type) [Fintype X] [LinearOrder X] (hX : Fintype.card X = d) :
    #(univ.filter fun k : X × X => k.1 < k.2) ≤ d ^ 2 :=
  (card_le_univ _).trans_eq (by rw [Fintype.card_prod, hX, sq])
end ClauseBound.Grid
