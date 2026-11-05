-- Prove2me | solution 1 for ClauseBound.Inst.Half.CertSmall.cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:08.405334+00:00
-- url     : https://prove2.me/submissions/1927a197-5cf6-4ea3-9f4a-7fb5c4d56e6a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_sOf_polyT
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_clog_polyT
import Theorems.Thm_ClauseBound_Inst_Half_RcolF_polyT
import Theorems.Thm_ClauseBound_Inst_Half_RrowF_polyT
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
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.CertSmall
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.CertSmall
theorem _root_.solution (c₀ c : ℕ) : Unary fun p : Bool × U × U × ℕ => (halfF c₀ c).cap p.1 p.2.1.length p.2.2.1.length p.2.2.2 := by
  have hl : Unary fun p : Bool × U × U × ℕ => p.2.2.1.length := Unary.of_length PolyT.id'.snd.snd.fst
  have hh : Unary fun p : Bool × U × U × ℕ => hF c₀ p.2.2.1.length := hF_unary c₀ hl
  have hs : PolyT fun p : Bool × U × U × ℕ => sOf (hF c₀ p.2.2.1.length) p.2.2.2 := sOf_polyT hh.poly PolyT.id'.snd.snd.snd
  have hb : Unary fun p : Bool × U × U × ℕ => 2 * c * p.2.2.1.length := (Unary.const (2 * c)).mul hl
  have hR : PolyT fun p : Bool × U × U × ℕ => bif p.1 then RcolF (hF c₀ p.2.2.1.length) (sOf (hF c₀ p.2.2.1.length) p.2.2.2)
      else RrowF (hF c₀ p.2.2.1.length) (sOf (hF c₀ p.2.2.1.length) p.2.2.2) :=
    PolyT.cond' PolyT.id'.fst (RcolF_polyT hh hs) (RrowF_polyT hh hs)
  exact hb.of_le (PolyT.min' hb.poly (clog_polyT hR)) fun p => min_le_left _ _
end ClauseBound.Inst.Half.CertSmall
