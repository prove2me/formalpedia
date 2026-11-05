-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.GW_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:33.084391+00:00
-- url     : https://prove2.me/submissions/35453e94-4429-47d5-968b-67fe37977020

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_powZ_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_prod_range_polyT
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertOL
theorem _root_.solution {R : α → ℕ} {ws : α → List ℤ} {lo hi : α → List ℕ} {t : α → ℕ → ℕ} (hR : Unary R) (hws : PolyT ws) (hlo : PolyT lo) (hhi : PolyT hi)
    (ht : Unary fun p : α × ℕ => t p.1 p.2) : PolyT fun x => GW (R x) (ws x) (lo x) (hi x) (t x) := by
  have hj : PolyT fun p : α × ℕ => min p.2 (R p.1) := PolyT.min' PolyT.id'.snd (PolyT.comp hR.poly PolyT.id'.fst)
  have htj : Unary fun p : α × ℕ => t p.1 (min p.2 (R p.1)) := ht.comp (h := fun p : α × ℕ => (p.1, min p.2 (R p.1))) (PolyT.prodMk PolyT.id'.fst hj)
  have hl : PolyT fun p : α × ℕ => (lo p.1).getD (min p.2 (R p.1)) 0 := PolyT.getD (PolyT.comp hlo PolyT.id'.fst) hj (PolyT.const 0)
  have hh : PolyT fun p : α × ℕ => (hi p.1).getD (min p.2 (R p.1)) 0 := PolyT.getD (PolyT.comp hhi PolyT.id'.fst) hj (PolyT.const 0)
  have hw : PolyT fun p : α × ℕ => (ws p.1).getD (min p.2 (R p.1)) 0 := PolyT.getD (PolyT.comp hws PolyT.id'.fst) hj (PolyT.const 0)
  have hs : PolyT fun p : α × ℕ => if min p.2 (R p.1) = 0 then (1 : ℤ) else -1 :=
    PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) (PolyT.const 1) (PolyT.const (-1))
  unfold GW
  exact prod_range_polyT (f := fun x i => if (lo x).getD i 0 ≤ t x i ∧ t x i ≤ (hi x).getD i 0 then ((ws x).getD i 0 * (if i = 0 then 1 else -1)) ^ t x i else 0) hR
    (PolyT.ite' (PolyT.decide_and (PolyT.decide_le hl htj.poly) (PolyT.decide_le htj.poly hh)) (powZ_polyT (PolyT.mulZ hw hs) htj) (PolyT.const 0))
end ClauseBound.ParityChecks.CertOL
