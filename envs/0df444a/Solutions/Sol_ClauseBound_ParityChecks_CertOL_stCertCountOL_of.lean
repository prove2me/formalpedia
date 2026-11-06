-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertOL.stCertCountOL_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:21.34881+00:00
-- url     : https://prove2.me/submissions/0b5796f1-5701-4109-b7b5-3364d53f3fdc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_countOL_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_parQ_QU
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
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
namespace ClauseBound.ParityChecks.CertOL
theorem _root_.solution (hV : StCertValS) (hM : StCertMark) (hA : StCertAdm) (hD : StDec) : StCertCountOL := by
  intro Idx _ S hP k
  have hn : Unary fun x : U × Idx × (U × U) × Fml => x.2.2.1.1.length := Unary.of_length PolyT.id'.snd.snd.fst.fst
  have hΔ : Unary fun x : U × Idx × (U × U) × Fml => x.2.2.1.2.length := Unary.of_length PolyT.id'.snd.snd.fst.snd
  have hm : Unary fun x : U × Idx × (U × U) × Fml => x.2.2.2.length := Unary.of_length PolyT.id'.snd.snd.snd
  exact countOL_polyT (S := S) ⟨hV, hM, hA, hD, hP⟩ k (pad := fun x : U × Idx × (U × U) × Fml => x.1) (i := fun x => x.2.1)
    ⟨PolyT.id'.fst, PolyT.id'.snd.fst, hn, hΔ, parQ_QU hn hΔ hm⟩ PolyT.id'.snd.snd.snd
end ClauseBound.ParityChecks.CertOL
