-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.zNext_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:45.773268+00:00
-- url     : https://prove2.me/submissions/3475c856-4e86-459d-b4ad-2d11e52b8561

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution {cnt z B nP nR dP nof d p bits : α → ℕ} (h1 : PolyT cnt) (h2 : PolyT z) (h3 : PolyT B) (h4 : PolyT nP) (h5 : PolyT nR) (h6 : PolyT dP)
    (h7 : PolyT nof) (h8 : PolyT d) (h9 : PolyT p) (h10 : PolyT bits) :
    PolyT fun x => z x + nR x * Nat.size (dP x) + Nat.size (cnt x * nP x) + nof x + d x ^ 2 * (p x * B x + p x ^ 2 * bits x + 1) + 2 :=
  ((((h2.add (h5.mul (PolyT.size' h6))).add (PolyT.size' (h1.mul h4))).add h7).add
    ((PolyT.pow_const h8 2).mul (((h9.mul h3).add ((PolyT.pow_const h9 2).mul h10)).add (PolyT.const 1)))).add (PolyT.const 2)
end ClauseBound.Alg.CertLevel
