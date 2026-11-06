-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.bitOL_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:12:33.963695+00:00
-- url     : https://prove2.me/submissions/137061b0-4bb5-4ecb-afd9-2d13d95fa8ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_clog_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_blkOL_unary

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
variable {K n s D : α → ℕ}
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution (hD : Unary D) : Unary fun x => bitOL (D x) := by
  unfold bitOL
  exact clog_unary (blkOL_unary hD)
end ClauseBound.ParityChecks.CertTopOL
