-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.incL_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:43:32.863047+00:00
-- url     : https://prove2.me/submissions/6347b18c-e5e2-4015-b016-3fb0e046c394

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertOL
theorem _root_.solution {n j : α → ℕ} {ψ : α → Fml} {Lam : α → List (List ℕ)} (hn : PolyT n) (hψ : PolyT ψ) (hLam : PolyT Lam) (hj : Unary j) :
    PolyT fun x => incL (n x) (ψ x) (Lam x) (j x) := by
  have h1 : PolyT fun r : (α × ℕ) × ℕ => (ψ r.1.1).getD r.2 [] ++ [(n r.1.1 + r.1.2, false)] :=
    PolyT.append (PolyT.getD (PolyT.comp hψ PolyT.id'.fst.fst) PolyT.id'.snd (PolyT.const []))
      (PolyT.cons' (PolyT.prodMk (PolyT.add (PolyT.comp hn PolyT.id'.fst.fst) PolyT.id'.fst.snd) (PolyT.const false)) (PolyT.const []))
  have h2 : PolyT fun p : α × ℕ => ((Lam p.1).getD p.2 []).map fun e => (ψ p.1).getD e [] ++ [(n p.1 + p.2, false)] :=
    PolyT.map (f := fun (p : α × ℕ) e => (ψ p.1).getD e [] ++ [(n p.1 + p.2, false)]) h1 (PolyT.getD (PolyT.comp hLam PolyT.id'.fst) PolyT.id'.snd (PolyT.const []))
  have h3 : PolyT fun x => ((Lam x).getD (j x) []).map fun e => (ψ x).getD e [] :=
    PolyT.map (f := fun x e => (ψ x).getD e []) (PolyT.getD (PolyT.comp hψ PolyT.id'.fst) PolyT.id'.snd (PolyT.const [])) (PolyT.getD hLam hj.poly (PolyT.const []))
  unfold incL
  exact PolyT.append (PolyT.flatMap (f := fun x j' => ((Lam x).getD j' []).map fun e => (ψ x).getD e [] ++ [(n x + j', false)]) h2 (PolyT.range hj)) h3
end ClauseBound.ParityChecks.CertOL
