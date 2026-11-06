-- Prove2me | solution 1 for Eight.Level.Cert.factor_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:06.185033+00:00
-- url     : https://prove2.me/submissions/de9a4891-070e-4672-acda-665907952206

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_Eight_Level_Cert
import Theorems.Thm_ClauseBound_Alg_CertGridG_gridFf_polyT
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped
open Eight.Level.Cert
variable {C : Type} [Enc C] {lam : C → ℕ}
namespace Eight.Level.Cert
theorem _root_.solution (h : StKeeps) (g : ℕ) (tr : Bool) (hl : Unary lam) :
    PolyT fun x : (C × ℕ) × FQ => gridFf eightF [] g g tr 0 (lam x.1.1) x.1.2 x.2 :=
  CertGridG.gridFf_polyT h (PolyT.const []) (Unary.const g) (Unary.const g) (PolyT.const tr) (Unary.const 0) (hl.comp PolyT.id'.fst.fst)
    PolyT.id'.fst.snd PolyT.id'.snd
end Eight.Level.Cert
