-- Prove2me | solution 1 for ClauseBound.Inst.Half.allTab_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:43:44.921474+00:00
-- url     : https://prove2.me/submissions/aa754149-2b4b-46d4-b0b5-77e766b0afae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_getD_map_range
import Theorems.Thm_ClauseBound_Inst_Half_foldl_roundT
import Theorems.Thm_ClauseBound_Part_partsLe_of_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {W E : ℕ} (h : E ≤ W) : (allTab W).getD E [] = partsOf E := by
  rw [allTab, foldl_roundT, tabK, getD_map_range _ _ (by omega), partsLe_of_le h]
end ClauseBound.Inst.Half
