-- Prove2me | solution 1 for ClauseBound.Inst.Half.encF_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:21:43.928608+00:00
-- url     : https://prove2.me/submissions/4d8d75a9-b89d-4735-a5dc-a4d72e0cf17e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_ClauseBound_Inst_Half_encF_eq_getElem

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) ∈ (allTab W).getD h [] := by
  rw [encF_eq_getElem hW hp x]
  exact List.getElem_mem _
end ClauseBound.Inst.Half
