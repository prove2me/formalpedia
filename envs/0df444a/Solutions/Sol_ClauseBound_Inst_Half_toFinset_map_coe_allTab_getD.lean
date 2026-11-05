-- Prove2me | solution 1 for ClauseBound.Inst.Half.toFinset_map_coe_allTab_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:48:47.933016+00:00
-- url     : https://prove2.me/submissions/6b8ce670-a6a7-4555-a796-ac81bef4f486

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_allTab_getD
import Theorems.Thm_ClauseBound_Boson_mem_P
import Theorems.Thm_ClauseBound_Part_mem_map_coe_partsOf
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {W E : ℕ} (h : E ≤ W) :
    (((allTab W).getD E []).map fun L : List ℕ => (L : Multiset ℕ)).toFinset = ClauseBound.Boson.P E := by
  ext τ
  rw [allTab_getD h, List.mem_toFinset, mem_map_coe_partsOf, ClauseBound.Boson.mem_P]
end ClauseBound.Inst.Half
