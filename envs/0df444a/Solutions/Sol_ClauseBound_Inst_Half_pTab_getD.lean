-- Prove2me | solution 1 for ClauseBound.Inst.Half.pTab_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:44:54.146045+00:00
-- url     : https://prove2.me/submissions/39e8ed79-19b6-4cb5-b253-aa82b6ba8db5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_getD_map_range
import Theorems.Thm_ClauseBound_Inst_Half_pTab_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution (W i : ℕ) (h : i ≤ W) : (pTab W).getD i 0 = Partitions.p i := by
  rw [pTab_eq, getD_map_range p 0 (by omega)]
end ClauseBound.Inst.Half
