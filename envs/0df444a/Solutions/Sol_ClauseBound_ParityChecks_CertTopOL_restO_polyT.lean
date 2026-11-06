-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.restO_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:12:35.180513+00:00
-- url     : https://prove2.me/submissions/aafa67a5-6791-4888-b651-2db21e51e74d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_blkOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_restO_aux
import Theorems.Thm_ClauseBound_TopN_Cert_betaN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_blockN_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] ClauseBound.TopN.Cert.betaN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.blockN_unary
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
variable {K n s D : α → ℕ}
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution (k : ℕ) (hK : Unary K) (hn : Unary n) (hs : Unary s) : PolyT fun x => restO k (K x) (n x) (s x) := by
  have hD := blockN_unary k hn hs
  have hn' := hn.poly
  unfold restO
  exact restO_aux k hK.poly (PolyT.size' ((blkOL_unary hD).poly.mul (((PolyT.const 7).mul hn').add (PolyT.const 1)))) (PolyT.size' (hD.poly.mul hn'))
    (betaN_unary k hs).poly (PolyT.size' hn') hn' (pow_polyT (PolyT.const 2) hs)
end ClauseBound.ParityChecks.CertTopOL
