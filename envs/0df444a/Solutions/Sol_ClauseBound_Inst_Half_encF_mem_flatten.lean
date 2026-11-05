-- Prove2me | solution 1 for ClauseBound.Inst.Half.encF_mem_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:17.713296+00:00
-- url     : https://prove2.me/submissions/5e1580fd-bc41-4d12-9a64-667a9256ea67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_ClauseBound_Inst_Half_encF_mem
import Theorems.Thm_ClauseBound_Inst_Half_mem_allTab_getD
import Theorems.Thm_ClauseBound_Inst_Half_mem_flatten_allTab


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) ∈ (allTab W).flatten := by
  have h1 := (mem_allTab_getD hW).1 (encF_mem hW hp x)
  exact mem_flatten_allTab.2 ⟨h1.1.trans_le hW, h1.2.1, h1.2.2⟩
end ClauseBound.Inst.Half
