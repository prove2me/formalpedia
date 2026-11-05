-- Prove2me | solution 1 for ClauseBound.Inst.Half.nodup_map_coe_allTab_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:47:24.285122+00:00
-- url     : https://prove2.me/submissions/77260602-09c5-4c48-9f00-d10cc7095b8a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_allTab_getD
import Theorems.Thm_ClauseBound_Part_nodup_map_coe_partsOf
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {W E : ℕ} (h : E ≤ W) : (((allTab W).getD E []).map fun L : List ℕ => (L : Multiset ℕ)).Nodup := by
  rw [allTab_getD h]
  exact nodup_map_coe_partsOf E
end ClauseBound.Inst.Half
