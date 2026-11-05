-- Prove2me | solution 1 for Eight.ViaGrouping.A_bitsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:27:12.08145+00:00
-- url     : https://prove2.me/submissions/0453c972-7fd7-498f-9748-cbabfd21747d

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
import Theorems.Thm_ClauseBound_Alg_GridPresents_bitsOf_bitsOf
import Theorems.Thm_Eight_stAMul
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {lam : ℕ} (i : ℕ) {X Y U V : List Bool} (hX : X.length = lam) (hY : Y.length = lam) (hU : U.length = lam) (hV : V.length = lam) :
    A lam i (Grid.bitsOf lam X) (Grid.bitsOf lam Y) (Grid.bitsOf lam U) (Grid.bitsOf lam V) = aMul (i, X, Y, U, V) := by
  rw [← stAMul]
  change aMul (i, ClauseBound.Alg.bitsOf (Grid.bitsOf lam X), ClauseBound.Alg.bitsOf (Grid.bitsOf lam Y), ClauseBound.Alg.bitsOf (Grid.bitsOf lam U), ClauseBound.Alg.bitsOf (Grid.bitsOf lam V)) = _
  rw [bitsOf_bitsOf hX, bitsOf_bitsOf hY, bitsOf_bitsOf hU, bitsOf_bitsOf hV]
end Eight.ViaGrouping
