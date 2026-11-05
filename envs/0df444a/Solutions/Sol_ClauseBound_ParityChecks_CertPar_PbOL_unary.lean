-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertPar.PbOL_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:11:27.570864+00:00
-- url     : https://prove2.me/submissions/96317154-0de7-4553-bbde-1e9eea0ae877

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_occOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_bitOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_Pb_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_g_unary
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
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
theorem _root_.solution {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => PbOL (K x) (n x) (Δ x) :=
  Pb_unary (g_unary hK) ((Unary.const 7).mul hn) (bitOL_unary hΔ) (occOL_unary hn.poly hΔ)
end ClauseBound.ParityChecks.CertPar
