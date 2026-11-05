-- Prove2me | solution 1 for ClauseBound.Alg.CertTopNet.stCertValS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:45:43.416601+00:00
-- url     : https://prove2.me/submissions/d1d10358-a888-4b38-9f23-6182a8818d5a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Theorems.Thm_ClauseBound_Alg_CertTopNet_lamS_unary
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertTopNet
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertTopNet
theorem _root_.solution (hR : StCertRebalG) : StCertValS := by
  intro Idx _ S hS C _ F hF α _ pad i Ub P c hp hi hU hP hc
  have hK : Unary fun x => S.K (i x) := hS.K.comp hi
  have hg : Unary fun x => 3 * S.K (i x) ^ 8 := (Unary.const 3).mul (unary_pow_const hK 8)
  have hl : Unary fun x => lamS (S.K (i x)) (3 * S.K (i x) ^ 8) (Ub x) (P x) := lamS_unary hK hg hU hP
  have h1 := hR C F hF α pad _ _ _ c hp hK hg hl hc
  have h2 : PolyT fun q : α × PInst => S.run (pad q.1, i q.1, q.2) :=
    PolyT.comp hS.run (PolyT.prodMk (PolyT.comp hp PolyT.id'.fst) (PolyT.prodMk (PolyT.comp hi PolyT.id'.fst) PolyT.id'.snd))
  unfold valS
  exact PolyT.optionElim h1 (PolyT.const 0) h2
end ClauseBound.Alg.CertTopNet
