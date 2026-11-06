-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.occOL_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:31.33275+00:00
-- url     : https://prove2.me/submissions/ea14f485-a9b6-4563-8173-27b09dcbb488

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_max_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_colMax_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_rowMax_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
variable {K n s D : α → ℕ}
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution (hn : Unary n) (hD : Unary D) : Unary fun x => occOL (n x) (D x) := by
  unfold occOL
  exact max_unary (hD.mul ((Unary.const 2).add (colMax_unary hn hD))) (rowMax_unary hn hD)
end ClauseBound.ParityChecks.CertTopOL
