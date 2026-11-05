-- Prove2me | solution 1 for ClauseBound.Inst.Half.ofWord_bitsOf_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:54.68021+00:00
-- url     : https://prove2.me/submissions/4e1849fe-3790-4534-89d5-1095fc8460f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_toWord_ofWord
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution {x v : Pieces.Bits lam} (e : ofWord (bitsOf x) = ofWord (bitsOf v)) : x = v := by
  have h1 := toWord_ofWord (bitsOf x)
  have h2 := toWord_ofWord (bitsOf v)
  rw [e, show (bitsOf x).length = (bitsOf v).length by rw [bitsOf, bitsOf, List.length_ofFn, List.length_ofFn], h2] at h1
  exact List.ofFn_injective h1.symm
end ClauseBound.Inst.Half
