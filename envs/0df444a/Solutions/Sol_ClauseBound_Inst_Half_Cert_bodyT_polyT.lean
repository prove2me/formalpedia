-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.bodyT_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:48.466832+00:00
-- url     : https://prove2.me/submissions/b71d2914-cd60-455c-9939-e4f0cbff6426

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_Cert_encF_polyT
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution (Ht : StTopF) (Hb : StBotF) {pad : α → U} {tr top : α → Bool} {h j : α → ℕ} {s : α → ℤ} {T : α → PT} {a b : α → List Bool}
    {τ : α → List ℕ} (hp : PolyT pad) (htr : PolyT tr) (htop : PolyT top) (hh : Unary h) (hs : PolyT s) (hT : PolyT T) (ha : PolyT a) (hb : PolyT b)
    (hj : Unary j) (hτ : PolyT τ) :
    PolyT fun x => bodyT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (j x) (τ x) := by
  have hW : Unary fun x => 4 * h x := (Unary.const 4).mul hh
  have hfl : PolyT fun x => (T x).flatten := PolyT.flatten hT
  have hea := encF_polyT hT hh.poly ha
  have heb := encF_polyT hT hh.poly hb
  have hr1 : PolyT fun x => s x - (h x : ℤ) + (j x : ℤ) := PolyT.addZ (PolyT.subZ hs (PolyT.natCast hh.poly)) (PolyT.natCast hj.poly)
  have hr2 : PolyT fun x => (h x : ℤ) - s x - (j x : ℤ) := PolyT.subZ (PolyT.subZ (PolyT.natCast hh.poly) hs) (PolyT.natCast hj.poly)
  exact PolyT.cond' htop
    (PolyT.cond' htr (Ht α pad _ h j _ _ _ _ _ hp hW hfl hh hea hj hr1 heb hτ) (Ht α pad _ h j _ _ _ _ _ hp hW hfl hh hea hj hr1 hτ heb))
    (PolyT.cond' htr (Hb α pad _ h _ _ _ _ _ hp hW hfl hh heb hr2 hτ hea) (Hb α pad _ h _ _ _ _ _ hp hW hfl hh heb hr2 hea hτ))
end ClauseBound.Inst.Half.Cert
