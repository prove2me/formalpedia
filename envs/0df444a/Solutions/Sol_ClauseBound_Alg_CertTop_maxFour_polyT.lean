-- Prove2me | solution 1 for ClauseBound.Alg.CertTop.maxFour_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:41:05.294858+00:00
-- url     : https://prove2.me/submissions/a8b90f91-2ab3-44a4-8fe4-21b77a2b94b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_CertCount
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ClauseBound_Alg_CertTop
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg.CertCount CountKSat CountKSat.Poly
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertTop
theorem _root_.solution {K P L v : α → ℕ} (hK : PolyT K) (hP : PolyT P) (hL : PolyT L) (hv : PolyT v) :
    PolyT fun x => max (max (3 * K x ^ 8 * Nat.size (K x)) (P x * (2 * (3 * K x ^ 8) / K x + 1))) (max ((K x - 1) * L x) (v x)) := by
  have hG : PolyT fun x => 3 * K x ^ 8 := PolyT.mul (PolyT.const 3) (PolyT.pow_const hK 8)
  exact PolyT.max' (PolyT.max' (PolyT.mul hG (PolyT.size' hK)) (PolyT.mul hP (PolyT.add (PolyT.div (PolyT.mul (PolyT.const 2) hG) hK) (PolyT.const 1))))
    (PolyT.max' (PolyT.mul (PolyT.sub hK (PolyT.const 1)) hL) hv)
end ClauseBound.Alg.CertTop
