-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.runToF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:57:15.145837+00:00
-- url     : https://prove2.me/submissions/a36ba60b-51b6-4cb1-8a69-2273045edd6c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_CU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_orcA_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_orcB_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_foldl_range_min
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PaddedDescent_F_foldl_cap
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
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
theorem _root_.solution {ψ : α → Fml} {Ls : α → List Chk} {e : α → ℕ} (hψ : PolyT ψ) (hL : PolyT Ls) (he : Unary e) :
    PolyT fun x => runToF S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) (Ls x) (e x) := by
  have hc1 := hc.comp (β := α × Chk × ℕ) PolyT.id'.fst
  have hA : PolyT fun r : (α × Chk × ℕ) × List Chk => orcA S k (pad r.1.1) (i r.1.1) (n r.1.1) (Δ r.1.1) (q r.1.1) (ψ r.1.1) r.2 :=
    orcA_polyT G k (hc.comp (β := (α × Chk × ℕ) × List Chk) PolyT.id'.fst.fst) (PolyT.comp hψ PolyT.id'.fst.fst) PolyT.id'.snd
  have hB : PolyT fun r : (α × Chk × ℕ) × List Chk × Chk × ℕ × ℕ =>
      orcB S k (pad r.1.1) (i r.1.1) (n r.1.1) (Δ r.1.1) (q r.1.1) (ψ r.1.1) r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 :=
    orcB_polyT G k (hc.comp (β := (α × Chk × ℕ) × List Chk × Chk × ℕ × ℕ) PolyT.id'.fst.fst) (PolyT.comp hψ PolyT.id'.fst.fst) PolyT.id'.snd.fst PolyT.id'.snd.snd.fst
      PolyT.id'.snd.snd.snd.fst PolyT.id'.snd.snd.snd.snd
  have hd : PolyT fun p : α × Chk × ℕ => (q p.1).decide1 (orcA S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1))
      (orcB S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1)) (Ls p.1) p.2.1 (min p.2.2 (e p.1)) :=
    G.dec (α × Chk × ℕ) _ hc1.q (fun p => orcA S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1))
      (fun p => orcB S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1)) _ _ _ hA hB (PolyT.comp hL PolyT.id'.fst) PolyT.id'.snd.fst
      (unary_min_right PolyT.id'.snd.snd (he.comp PolyT.id'.fst))
  have h := foldl_cap (pad := pad) (l := fun x => List.range (e x)) (a := fun _ => ([] : Chk))
    (g := fun x cur y => (q x).decide1 (orcA S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x)) (orcB S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x)) (Ls x) cur (min y (e x)))
    [] hc.pad (PolyT.range he) (PolyT.const []) hd
  refine h.congr fun x => ?_
  unfold runToF
  exact foldl_range_min (e x) (fun cur y => cap (pad x) [] ((q x).decide1 (orcA S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x))
    (orcB S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x)) (Ls x) cur y)) _
end ClauseBound.ParityChecks.CertOL
