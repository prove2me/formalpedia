-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertPar.parM_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:03.848468+00:00
-- url     : https://prove2.me/submissions/c249f09c-9f83-4b18-8258-c7206758086f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_capM_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_blkOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_bitOL_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_PaddedDescent_F_CertGrid_capM_unary
attribute [local fun_prop] Groundwork.PolyT.prodMk



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertPar
theorem _root_.solution {q : α → Par} (hq : QU q) {n Δ : α → ℕ} (hn : Unary n) (hΔ : Unary Δ) : PolyT fun x => parM (n x) (Δ x) (q x) :=
  PolyT.prodMk (hn.add hq.r) (PolyT.prodMk (capM_unary hq) (PolyT.prodMk (bitOL_unary hΔ) (blkOL_unary hΔ)))
end ClauseBound.ParityChecks.CertPar
