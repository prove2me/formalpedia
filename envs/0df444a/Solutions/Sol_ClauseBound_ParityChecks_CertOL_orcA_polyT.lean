-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.orcA_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:48:40.172228+00:00
-- url     : https://prove2.me/submissions/eead6485-ce59-4f2d-bfcb-e347a1cafb26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_incL_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_evW_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_div_two_pow_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_capM_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_PaddedDescent_F_CertGrid_capM_unary
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
variable (G : Given S) (k : ℕ) {pad : α → U} {i : α → Idx} {n Δ : α → ℕ} {q : α → Par} (hc : CU pad i n Δ q)
include G hc
namespace ClauseBound.ParityChecks.CertOL
theorem _root_.solution {ψ : α → Fml} {Ls : α → List Chk} (hψ : PolyT ψ) (hL : PolyT Ls) :
    PolyT fun x => orcA S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) (Ls x) := by
  have hnb : PolyT fun x => (q x).nb + 1 := PolyT.add hc.q.nb.poly (PolyT.const 1)
  have hlen : Unary fun x => (Ls x).length := Unary.of_length hL
  unfold orcA
  exact div_two_pow_polyT (evW_polyT G k hc (PolyT.const [1, -2]) (PolyT.cons' hnb (PolyT.const [0]))
    (PolyT.cons' hnb (PolyT.cons' (capM_unary hc.q).poly (PolyT.const [])))
    (PolyT.cons' hψ (PolyT.cons' (incL_polyT hc.n.poly hψ (PolyT.take hlen.poly hL) hlen) (PolyT.const [])))) hc.q.r
end ClauseBound.ParityChecks.CertOL
