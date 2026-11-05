-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.partH_polyT_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:45.507807+00:00
-- url     : https://prove2.me/submissions/68af1bf8-7220-463a-9c0f-13c65016d3f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_Cert_sOf_polyT
import Theorems.Thm_ClauseBound_Inst_Half_Cert_partT_polyT
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_sOf_polyT
import Theorems.Thm_ClauseBound_Inst_Half_allTabF_polyT
import Theorems.Thm_ClauseBound_Inst_Half_hF_unary
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution (Ht : StTopF) (Hb : StBotF) (c₀ : ℕ) (top : Bool) : PolyT (partH c₀ top) := by
  have hl : Unary fun q : PQ => q.2.2.1.length := Unary.of_length PolyT.id'.snd.snd.fst
  have hh : Unary fun q : PQ => hF c₀ q.2.2.1.length := hF_unary c₀ hl
  have hpad : PolyT fun q : PQ => q.1.1 := PolyT.id'.fst.fst
  exact partT_polyT Ht Hb hpad PolyT.id'.fst.snd (PolyT.const top) hh (sOf_polyT hh.poly PolyT.id'.snd.fst.snd)
    (allTabF_polyT hpad ((Unary.const 4).mul hh)) PolyT.id'.snd.snd.fst PolyT.id'.snd.snd.snd.fst PolyT.id'.snd.snd.snd.snd
end ClauseBound.Inst.Half.Cert
