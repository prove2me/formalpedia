-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertPar.i0Of_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:27:49.221611+00:00
-- url     : https://prove2.me/submissions/173ba58b-6afe-4720-844d-b1f82e6e5845

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_log_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_log_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertPar
theorem _root_.solution {n : α → ℕ} (hn : Unary n) : Unary fun x => i0Of (n x) :=
  unary_div (unary_sub (((Unary.const 20).mul hn).add (log_unary hn)) (PolyT.const 1)) (log_polyT hn.poly)
end ClauseBound.ParityChecks.CertPar
