-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertNum.numR_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:30.217252+00:00
-- url     : https://prove2.me/submissions/689c3581-70ad-4892-81b9-b3c2b7134127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertNum
theorem _root_.solution {m nb r : α → ℕ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hL : PolyT Ls)
    (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => ((Ls x).map fun L => 2 ^ L.length * nb x ^ m x).sum + 2 ^ (cur x).length * nb x ^ e x * (nb x + 1) ^ (m x - e x) +
      (r x - 1 - (Ls x).length) * (nb x + 1) ^ m x := by
  have hn1 : PolyT fun x => nb x + 1 := PolyT.add hnb.poly (PolyT.const 1)
  have h1 : PolyT fun p : α × Chk => 2 ^ p.2.length * nb p.1 ^ m p.1 :=
    PolyT.mul (PolyT.pow_unary (PolyT.const 2) (Unary.of_length PolyT.id'.snd))
      (PolyT.pow_unary (PolyT.comp hnb.poly PolyT.id'.fst) (hm.comp PolyT.id'.fst))
  have h2 : PolyT fun x => (Ls x).map fun L => 2 ^ L.length * nb x ^ m x := PolyT.map h1 hL
  have t2 : PolyT fun x => 2 ^ (cur x).length * nb x ^ e x * (nb x + 1) ^ (m x - e x) :=
    PolyT.mul (PolyT.mul (PolyT.pow_unary (PolyT.const 2) (Unary.of_length hc)) (PolyT.pow_unary hnb.poly he)) (PolyT.pow_unary hn1 (unary_sub hm he.poly))
  have t3 : PolyT fun x => (r x - 1 - (Ls x).length) * (nb x + 1) ^ m x :=
    PolyT.mul (PolyT.sub (PolyT.sub hr.poly (PolyT.const 1)) (PolyT.length hL)) (PolyT.pow_unary hn1 hm)
  exact PolyT.add (PolyT.add (PolyT.sum h2) t2) t3
end ClauseBound.ParityChecks.CertNum
