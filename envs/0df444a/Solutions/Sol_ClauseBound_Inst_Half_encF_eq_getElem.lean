-- Prove2me | solution 1 for ClauseBound.Inst.Half.encF_eq_getElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:14:47.818205+00:00
-- url     : https://prove2.me/submissions/d0ed2c9f-9cd3-4779-ae1b-844eb47339c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) = ((allTab W).getD h [])[ofWord (bitsOf x)]'(ofWord_bitsOf_lt_length hW hp x) :=
  List.getD_eq_getElem _ _ _
end ClauseBound.Inst.Half
