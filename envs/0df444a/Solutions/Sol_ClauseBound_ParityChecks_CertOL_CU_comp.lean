-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.CU.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:47.1688+00:00
-- url     : https://prove2.me/submissions/9374383a-7f08-43cc-99ae-0a8862957b7a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace ClauseBound.ParityChecks.CertOL
namespace CU
theorem _root_.solution {β : Type} [Enc β] {pad : α → U} {i : α → Idx} {n Δ : α → ℕ} {q : α → Par} (h : CU pad i n Δ q) {g : β → α} (hg : PolyT g) :
    CU (fun y => pad (g y)) (fun y => i (g y)) (fun y => n (g y)) (fun y => Δ (g y)) (fun y => q (g y)) :=
  ⟨PolyT.comp h.pad hg, PolyT.comp h.i hg, h.n.comp hg, h.Δ.comp hg, h.q.comp hg⟩
end CU
end ClauseBound.ParityChecks.CertOL
