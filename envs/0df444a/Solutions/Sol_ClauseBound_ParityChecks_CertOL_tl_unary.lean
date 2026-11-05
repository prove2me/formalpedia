-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.tl_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:39.130223+00:00
-- url     : https://prove2.me/submissions/355d68c4-59c9-4b83-bb93-23703949b6ab

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
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Prog_NetE_unary_sum_map
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mu_unary
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mu_unary



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertOL
theorem _root_.solution {g y i : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hL : PolyT Ls) (hy : PolyT y) (hi : PolyT i) :
    Unary fun x => tl (g x) (Ls x) (y x) (i x) :=
  unary_sum_map (f := fun x a => mu (g x) (Ls x) (y x) a a (i x))
    (Mark.Cert.mu_unary (PolyT.comp hg.poly PolyT.id'.fst) (PolyT.comp hL PolyT.id'.fst) (PolyT.comp hy PolyT.id'.fst) PolyT.id'.snd PolyT.id'.snd
      (PolyT.comp hi PolyT.id'.fst)) (PolyT.range hg)
end ClauseBound.ParityChecks.CertOL
