-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.encF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:36:43.228921+00:00
-- url     : https://prove2.me/submissions/6d9f4168-73ce-43ac-8598-b9e4f8c1b786

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
import Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution {T : α → PT} {h : α → ℕ} {a : α → List Bool} (hT : PolyT T) (hh : PolyT h) (ha : PolyT a) : PolyT fun x => encF (T x) (h x) (a x) :=
  PolyT.getD (PolyT.getD hT hh (PolyT.const [])) (PolyT.ofWord' ha) (PolyT.const [])
end ClauseBound.Inst.Half.Cert
