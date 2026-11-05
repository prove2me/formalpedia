-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.clog_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:26:06.802814+00:00
-- url     : https://prove2.me/submissions/ebcb092e-c0c2-414c-b3c5-b7854404ad12

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_ClauseBound_Inst_Rec_clog_two_eq
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution (n : ℕ) : Nat.clog 2 n ≤ n := by
  rw [ClauseBound.Inst.Rec.clog_two_eq]
  exact (Nat.size_le.2 Nat.lt_two_pow_self).trans (Nat.sub_le _ _)
end ClauseBound.ParityChecks.CertTopOL
