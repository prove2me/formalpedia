-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.partT_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:51:53.591768+00:00
-- url     : https://prove2.me/submissions/694e97f1-8fe2-4b53-8243-e0d85f0c4565

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_Cert_labs_polyT
import Theorems.Thm_ClauseBound_Inst_Half_Cert_partT_eq
import Theorems.Thm_ClauseBound_Inst_Half_Cert_bodyT_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_unary_min_right
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] ClauseBound.Inst.Rec.unary_min_right
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution (Ht : StTopF) (Hb : StBotF) {pad : α → U} {tr top : α → Bool} {h : α → ℕ} {s : α → ℤ} {T : α → PT} {a b θ : α → List Bool}
    (hp : PolyT pad) (htr : PolyT tr) (htop : PolyT top) (hh : Unary h) (hs : PolyT s) (hT : PolyT T) (ha : PolyT a) (hb : PolyT b) (hθ : PolyT θ) :
    PolyT fun x => partT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (θ x) := by
  have h1 : PolyT fun x => (labs (T x) (tr x) (h x) (s x))[ofWord (θ x)]? := PolyT.getElem? (labs_polyT hT htr hh hs) (PolyT.ofWord' hθ)
  have hj : Unary fun q : α × ℕ × List ℕ => min q.2.1 (2 * h q.1) :=
    unary_min_right PolyT.id'.snd.fst ((Unary.const 2).mul (hh.comp PolyT.id'.fst))
  have h2 : PolyT fun q : α × ℕ × List ℕ => bodyT (pad q.1) (tr q.1) (top q.1) (h q.1) (s q.1) (T q.1) (a q.1) (b q.1) (min q.2.1 (2 * h q.1)) q.2.2 :=
    bodyT_polyT Ht Hb (PolyT.comp hp PolyT.id'.fst) (PolyT.comp htr PolyT.id'.fst) (PolyT.comp htop PolyT.id'.fst) (hh.comp PolyT.id'.fst)
      (PolyT.comp hs PolyT.id'.fst) (PolyT.comp hT PolyT.id'.fst) (PolyT.comp ha PolyT.id'.fst) (PolyT.comp hb PolyT.id'.fst) hj PolyT.id'.snd.snd
  exact (PolyT.optionElim (f := fun x (p : ℕ × List ℕ) => bodyT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (min p.1 (2 * h x)) p.2)
    h1 (PolyT.const 0) h2).congr fun x => (partT_eq _ _ _ _ _ _ _ _ _).symm
end ClauseBound.Inst.Half.Cert
