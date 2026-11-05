-- Prove2me | solution 1 for ClauseBound.Inst.Half.encF_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:08.498793+00:00
-- url     : https://prove2.me/submissions/a6dee3e3-2702-4e35-a7ab-b125e1cff8ac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_ClauseBound_Inst_Half_encF_mem
import Theorems.Thm_ClauseBound_Inst_Half_mem_allTab_getD
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    ClauseBound.Boson.Pos (encF (allTab W) h (bitsOf x)) ∧ (encF (allTab W) h (bitsOf x)).sum = h := by
  have h1 := (mem_allTab_getD hW).1 (encF_mem hW hp x)
  exact ⟨h1.2.1, h1.1⟩
end ClauseBound.Inst.Half
