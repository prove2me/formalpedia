-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.wOf_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:36:42.17423+00:00
-- url     : https://prove2.me/submissions/b032efb2-4d03-40c5-9364-b1f40928e15c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution {tr : α → Bool} {h j : α → ℕ} {s : α → ℤ} (ht : PolyT tr) (hh : PolyT h) (hs : PolyT s) (hj : PolyT j) :
    PolyT fun x => wOf (tr x) (h x) (s x) (j x) :=
  PolyT.cond' ht (PolyT.subZ (PolyT.subZ (PolyT.mulZ (PolyT.const 2) (PolyT.natCast hh)) hs) (PolyT.natCast hj)) (PolyT.addZ hs (PolyT.natCast hj))
end ClauseBound.Inst.Half.Cert
