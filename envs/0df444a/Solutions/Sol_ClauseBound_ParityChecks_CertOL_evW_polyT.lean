-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.evW_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:02.577757+00:00
-- url     : https://prove2.me/submissions/37a27b15-d876-492a-b237-70f793ba50de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_tl_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_GW_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_CU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_PbOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_UbOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_g_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_parM_polyT
import Theorems.Thm_ClauseBound_TopN_Cert_evalV_polyT
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
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
theorem _root_.solution {ws : α → List ℤ} {lo hi : α → List ℕ} {Ls : α → List Fml} (hws : PolyT ws) (hlo : PolyT lo) (hhi : PolyT hi) (hL : PolyT Ls) :
    PolyT fun x => evW S k (pad x) (i x) (n x) (Δ x) (q x) (ws x) (lo x) (hi x) (Ls x) := by
  have hK : Unary fun x => S.K (i x) := G.poly.K.comp hc.i
  have hc' := hc.comp (β := α × MCtx) PolyT.id'.fst
  have hK' : Unary fun r : α × MCtx => S.K (i r.1) := hK.comp PolyT.id'.fst
  have hgw : PolyT fun r : α × MCtx => GW r.2.2.1.length (ws r.1) (lo r.1) (hi r.1) (tl r.2.1.1.length r.2.2.1 r.2.2.2) :=
    GW_polyT (t := fun (r : α × MCtx) j => tl r.2.1.1.length r.2.2.1 r.2.2.2 j) (Unary.of_length PolyT.id'.snd.snd.fst) (PolyT.comp hws PolyT.id'.fst)
      (PolyT.comp hlo PolyT.id'.fst) (PolyT.comp hhi PolyT.id'.fst)
      (tl_unary (Unary.of_length PolyT.id'.fst.snd.fst.fst) PolyT.id'.fst.snd.snd.fst PolyT.id'.fst.snd.snd.snd PolyT.id'.snd)
  have hv : PolyT fun r : α × MCtx => valS S (pad r.1) (i r.1) (UbOL k (S.K (i r.1)) (n r.1) (Δ r.1)) (PbOL (S.K (i r.1)) (n r.1) (Δ r.1)) markF r.2 :=
    G.val Idx S G.poly MCtx markF G.mark (α × MCtx) _ _ _ _ _ hc'.pad hc'.i (UbOL_unary k hK' hc'.n hc'.Δ) (PbOL_unary hK' hc'.n hc'.Δ) PolyT.id'.snd
  unfold evW
  exact ClauseBound.TopN.Cert.evalV_polyT (gu := fun x => rep (3 * S.K (i x) ^ 8))
    (val := fun x c => GW c.2.1.length (ws x) (lo x) (hi x) (tl c.1.1.length c.2.1 c.2.2) *
      valS S (pad x) (i x) (UbOL k (S.K (i x)) (n x) (Δ x)) (PbOL (S.K (i x)) (n x) (Δ x)) markF c)
    (k + 1) G.adm hc.pad (g_unary hK) (PolyT.mulZ hgw hv) (parM_polyT hc.q hc.n hc.Δ) hL
end ClauseBound.ParityChecks.CertOL
