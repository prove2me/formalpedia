-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.runF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:06:15.643636+00:00
-- url     : https://prove2.me/submissions/afc784a9-f04e-4121-a21a-13bf6f5e168a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_CU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_runToF_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PaddedDescent_F_foldl_cap
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



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
theorem _root_.solution {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => runF S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) := by
  have hc1 := hc.comp (β := α × List Chk × ℕ) PolyT.id'.fst
  have h1 : PolyT fun p : α × List Chk × ℕ => runToF S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1) p.2.1 (q p.1).m :=
    runToF_polyT G k hc1 (PolyT.comp hψ PolyT.id'.fst) PolyT.id'.snd.fst hc1.q.m
  unfold runF
  exact foldl_cap (pad := pad) (l := fun x => List.range (q x).r) (a := fun _ => ([] : List Chk))
    (g := fun x Ls _ => Ls ++ [runToF S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) Ls (q x).m]) [] hc.pad (PolyT.range hc.q.r) (PolyT.const [])
    (PolyT.append PolyT.id'.snd.fst (PolyT.cons' h1 (PolyT.const [])))
end ClauseBound.ParityChecks.CertOL
