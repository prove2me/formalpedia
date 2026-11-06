-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.clog_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:46.244699+00:00
-- url     : https://prove2.me/submissions/11fa5c18-fac3-4b3f-ab2e-18a29db76ce9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_clog_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_clog_le_self
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution {f : α → ℕ} (hf : Unary f) : Unary fun x => Nat.clog 2 (f x) :=
  hf.of_le (clog_polyT hf.poly) fun _ => clog_le_self _
end ClauseBound.ParityChecks.CertTopOL
