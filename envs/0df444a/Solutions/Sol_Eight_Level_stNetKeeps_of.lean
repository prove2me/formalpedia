-- Prove2me | solution 1 for Eight.Level.stNetKeeps_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:15:27.217196+00:00
-- url     : https://prove2.me/submissions/a825db0c-b410-45a3-a964-3428b3aad3fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_Eight_Level_Cert
import Theorems.Thm_Eight_Level_Cert_factor_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_capG_unary
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped
namespace Eight.Level
theorem _root_.solution (h : StKeeps) : StNetKeeps := fun g tr C _ _ _ _ _ hl ⟨_⟩ =>
  { n := (Unary.const (nMemb g g tr * (g * g))).mul (hl.comp (h := fun p : (C × ℕ) × ℕ => p.1.1) PolyT.id'.fst.fst)
    cap := CertGridG.capG_unary h (Unary.const g) (Unary.const g) (PolyT.const tr) (Unary.const 0)
      (hl.comp (h := fun p : (C × ℕ) × ℕ × ℕ => p.1.1) PolyT.id'.fst.fst) PolyT.id'.fst.snd PolyT.id'.snd.fst PolyT.id'.snd.snd
    W := ⟨IsPolyT.sideWP g tr hl.poly⟩
    f := ⟨IsPolyT.ofFun (Cert.factor_polyT h g tr hl)⟩ }
end Eight.Level
