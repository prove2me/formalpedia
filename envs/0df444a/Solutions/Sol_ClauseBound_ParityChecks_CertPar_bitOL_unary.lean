-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertPar.bitOL_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:46:46.594337+00:00
-- url     : https://prove2.me/submissions/d14dff0f-aedd-4690-9a09-5817b0e3fdce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_blkOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_unary
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertPar
theorem _root_.solution {Δ : α → ℕ} (hΔ : Unary Δ) : Unary fun x => bitOL (Δ x) := clog_unary (blkOL_unary hΔ).poly
end ClauseBound.ParityChecks.CertPar
