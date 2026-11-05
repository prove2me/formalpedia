-- Prove2me | solution 1 for ClauseBound.Inst.Half.sum_toFinset_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:23:10.687213+00:00
-- url     : https://prove2.me/submissions/b9f541ef-8120-4589-9752-5867efe7a41a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution (π : List ℕ) (g : ℕ → ℤ) : ∑ l ∈ (π : Multiset ℕ).toFinset, g l = (π.dedup.map g).sum := by
  rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.coe_dedup, Multiset.map_coe, Multiset.sum_coe]
end ClauseBound.Inst.Half
