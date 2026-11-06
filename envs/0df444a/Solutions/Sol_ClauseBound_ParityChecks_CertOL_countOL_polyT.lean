-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.countOL_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:27.71045+00:00
-- url     : https://prove2.me/submissions/39c8b391-d961-4ad8-9be6-301ab9de39d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_incL_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_evW_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_runF_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_div_two_pow_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_mod_two_pow_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_capM_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_PaddedDescent_F_CertGrid_capM_unary
attribute [local fun_prop] Groundwork.PolyT.const
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
theorem _root_.solution {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => countOL S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) := by
  have hr := runF_polyT G k hc hψ
  unfold countOL
  exact PolyT.toNat (mod_two_pow_polyT (div_two_pow_polyT (evW_polyT G k hc (PolyT.const [-1, -2]) (PolyT.const [0, 0])
    (PolyT.cons' hc.q.nb.poly (PolyT.cons' (capM_unary hc.q).poly (PolyT.const [])))
    (PolyT.cons' hψ (PolyT.cons' (incL_polyT hc.n.poly hψ (PolyT.take hc.q.r.poly hr) hc.q.r) (PolyT.const [])))) hc.q.r) (hc.n.add (Unary.const 1)))
end ClauseBound.ParityChecks.CertOL
