-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertNum.num_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:59:46.212802+00:00
-- url     : https://prove2.me/submissions/70e9ac96-0635-46e8-b3a9-883d48339b18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_ClauseBound_ParityChecks_CertNum_numP_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertNum_numI_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertNum_numR_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertNum_numC_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertNum_num_aux
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertNum
theorem _root_.solution {q : α → Par} (hq : QU q) {A : α → ℤ} {B : α → ℕ → ℤ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hA : PolyT A)
    (hB : PolyT fun p : α × ℕ => B p.1 p.2) (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).num (A x) (B x) (Ls x) (cur x) (e x) := by
  unfold Par.num Par.k
  exact num_aux hq.m hq.nb hq.r hq.i₀ (PolyT.length hL) (numP_polyT hq hA hB) (numI_polyT hq hL hc he.poly) (numR_polyT hq hL hc he)
    (numC_polyT hq hL hc he.poly)
end ClauseBound.ParityChecks.CertNum
