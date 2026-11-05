-- Prove2me | solution 1 for ClauseBound.Inst.Half.RrowF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:50:42.778671+00:00
-- url     : https://prove2.me/submissions/6c93d0d1-4c8b-4f7b-9885-bb1d0b2d2a1e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_sum_map_range
import Theorems.Thm_ClauseBound_Inst_Half_pzF_pTab

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {h : ℕ} {s : ℤ} (hs : s ≤ 2 * h) : RrowF h s = Rrow h s := by
  unfold RrowF Rrow
  rw [sum_map_range]
  refine Finset.sum_congr rfl fun i hi => pzF_pTab ?_
  have := Finset.mem_range.1 hi
  push_cast
  omega
end ClauseBound.Inst.Half
