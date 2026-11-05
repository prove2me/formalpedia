-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.labs_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:21.614418+00:00
-- url     : https://prove2.me/submissions/5966cecb-2869-499a-9354-18875b3bce4b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_Cert_wOf_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution {T : α → PT} {tr : α → Bool} {h : α → ℕ} {s : α → ℤ} (hT : PolyT T) (ht : PolyT tr) (hh : Unary h) (hs : PolyT s) :
    PolyT fun x => labs (T x) (tr x) (h x) (s x) := by
  have hr : PolyT fun x => List.range (2 * h x + 1) := PolyT.range (((Unary.const 2).mul hh).add (Unary.const 1))
  have hw : PolyT fun q : α × ℕ => wOf (tr q.1) (h q.1) (s q.1) q.2 :=
    wOf_polyT (PolyT.comp ht PolyT.id'.fst) (PolyT.comp hh.poly PolyT.id'.fst) (PolyT.comp hs PolyT.id'.fst) PolyT.id'.snd
  have hl : PolyT fun q : α × ℕ => (T q.1).getD (wOf (tr q.1) (h q.1) (s q.1) q.2).toNat [] :=
    PolyT.getD (PolyT.comp hT PolyT.id'.fst) (PolyT.toNat hw) (PolyT.const [])
  have hm : PolyT fun q : α × ℕ => ((T q.1).getD (wOf (tr q.1) (h q.1) (s q.1) q.2).toNat []).map fun τ => (q.2, τ) :=
    PolyT.map (f := fun (q : α × ℕ) (τ : List ℕ) => (q.2, τ)) (PolyT.prodMk PolyT.id'.fst.snd PolyT.id'.snd) hl
  have hf : PolyT fun q : α × ℕ => if 0 ≤ wOf (tr q.1) (h q.1) (s q.1) q.2 then
      ((T q.1).getD (wOf (tr q.1) (h q.1) (s q.1) q.2).toNat []).map fun τ => (q.2, τ) else [] :=
    PolyT.ite' (PolyT.decide_leZ (PolyT.const 0) hw) hm (PolyT.const [])
  unfold labs
  exact PolyT.flatMap (f := fun x j => if 0 ≤ wOf (tr x) (h x) (s x) j then ((T x).getD (wOf (tr x) (h x) (s x) j).toNat []).map fun τ => (j, τ) else []) hf hr
end ClauseBound.Inst.Half.Cert
