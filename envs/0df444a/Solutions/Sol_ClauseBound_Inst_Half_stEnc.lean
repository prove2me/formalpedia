-- Prove2me | solution 1 for ClauseBound.Inst.Half.stEnc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:32:54.057214+00:00
-- url     : https://prove2.me/submissions/d217e75d-9fc5-41d0-bc91-308fd3e8380b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_ClauseBound_Inst_Half_encF_ok
import Theorems.Thm_ClauseBound_Inst_Half_encF_mem_flatten
import Theorems.Thm_ClauseBound_Inst_Half_encF_inj

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution : StEnc := fun _ h _ hp =>
  ⟨fun x => ⟨(encF_ok (by omega) hp x).1, (encF_ok (by omega) hp x).2, encF_mem_flatten (by omega) hp x⟩,
    fun x v e => encF_inj (W := 4 * h) (by omega) hp x v e⟩
end ClauseBound.Inst.Half
