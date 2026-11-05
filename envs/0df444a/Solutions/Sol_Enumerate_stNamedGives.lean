-- Prove2me | solution 1 for Enumerate.stNamedGives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:54.778226+00:00
-- url     : https://prove2.me/submissions/85a02c84-c4c7-48c9-aaea-b52e7e32dc1e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_SparsificationLemma_Mach_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Enumerate_Named
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_SparsificationLemma_Mach_isKCNF_toN
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing
namespace Enumerate
theorem _root_.solution : StNamedGives := by
  rintro ⟨M, hfin, h⟩
  refine ⟨⟨M, hfin, fun ε hε => ?_⟩, fun ε hε => ?_⟩
  · obtain ⟨Mε, s, c, h1, hE, hrun⟩ := h ε hε
    refine ⟨Mε, s, c, h1, fun n φ h3 hne => ?_⟩
    obtain ⟨T, hT, hTle⟩ := hrun n φ h3 hne
    have hk : IsKCNF 3 n (Decode.toN φ) := isKCNF_toN h3.1 hne
    refine ⟨produced (tauOf s) n (Decode.toN φ), T, hT, hTle, hE.few n _ hk, hE.sparse n _ hk, ?_⟩
    rw [← Decode.satN_toN]
    exact hE.sat n _ hk
  · obtain ⟨Mε, s, -, h1, hE, -⟩ := h ε hε
    exact ⟨Mε, tauOf s, h1, hE⟩
end Enumerate
