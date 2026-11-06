-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.stCertCountOL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:55.931191+00:00
-- url     : https://prove2.me/submissions/7a715a41-bca3-4ca6-bc04-931e003b76ba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_stCertCountOL_of
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_stDec

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertOL
theorem _root_.solution (hV : StCertValS) (hM : StCertMark) (hA : StCertAdm) : StCertCountOL := stCertCountOL_of hV hM hA stDec
end ClauseBound.ParityChecks.CertOL
