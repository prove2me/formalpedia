-- Prove2me | solution 1 for Eight.ViaGrouping.stGridPsiPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:39:06.978085+00:00
-- url     : https://prove2.me/submissions/c537ce5c-2e28-4f93-9766-de0b5f92678a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_GridPsiDefs
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_SecCrossing_Cert
import Definitions.Def_Eight_Level_Presents
import Definitions.Def_Eight_Level_Cert
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Theorems.Thm_Eight_ViaGrouping_gridPsi_polyT
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution : StGridPsiPoly := fun g tr _ _ _ hl => gridPsi_polyT g tr (hl.poly.comp PolyT.id'.fst.fst) PolyT.id'.fst.snd PolyT.id'.snd
end Eight.ViaGrouping
