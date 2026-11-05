-- Prove2me | solution 1 for ClauseBound.Inst.Half.Pad.length_flatten_allTab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:05.998438+00:00
-- url     : https://prove2.me/submissions/85e4a38b-749d-4adf-abb7-83edc8bcca25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_ClauseBound_Inst_Half_foldl_roundT
import Theorems.Thm_ClauseBound_Inst_Half_sum_map_range
import Theorems.Thm_ClauseBound_Part_length_partsOf
import Theorems.Thm_ClauseBound_Part_partsLe_of_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_sum_map_range
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad
namespace ClauseBound.Inst.Half.Pad
theorem _root_.solution (W : ℕ) : (allTab W).flatten.length = ∑ E ∈ Finset.range (W + 1), p E := by
  have h : allTab W = tabK W W := foldl_roundT W W
  rw [h, tabK, List.length_flatten, List.map_map, sum_map_range]
  refine Finset.sum_congr rfl fun E hE => ?_
  have hE' : E ≤ W := Nat.lt_succ_iff.1 (Finset.mem_range.1 hE)
  rw [Function.comp_apply, partsLe_of_le hE', length_partsOf]
end ClauseBound.Inst.Half.Pad
