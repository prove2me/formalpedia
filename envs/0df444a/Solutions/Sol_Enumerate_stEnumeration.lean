-- Prove2me | solution 1 for Enumerate.stEnumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:13.179505+00:00
-- url     : https://prove2.me/submissions/d47081d8-8e4c-4420-ada2-3d2e7bf3a531

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_Enumerate_Enumeration
import Theorems.Thm_Enumerate_stEnumeratesTau
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Geo_stTauE


set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo
namespace Enumerate
theorem _root_.solution : StEnumeration := by
  intro ε hε
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have h0 : 0 < q := by exact_mod_cast hq0
  have h1 : q ≤ 1 := by exact_mod_cast (hq1.trans_le (min_le_right _ _)).le
  obtain ⟨a, b, -⟩ := stTauE 3 q (by norm_num) h0 h1
  rw [Nat.cast_ofNat] at b
  exact ⟨tauE 3 q ^ 6, tauE 3 q, Nat.one_le_pow _ _ (by omega), stEnumeratesTau (tauE 3 q) ε (by omega) (b.trans (hq1.trans_le (min_le_left _ _)).le)⟩
end Enumerate
