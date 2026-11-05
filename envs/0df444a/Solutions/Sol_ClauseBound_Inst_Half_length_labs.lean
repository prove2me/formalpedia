-- Prove2me | solution 1 for ClauseBound.Inst.Half.length_labs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:36:25.988909+00:00
-- url     : https://prove2.me/submissions/0e4c3c6f-2ea5-4320-8a4a-8e4615270991

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_ClauseBound_Inst_Half_toNat_wOf_le
import Theorems.Thm_ClauseBound_Inst_Half_length_allTab_getD
import Theorems.Thm_ClauseBound_Inst_Half_sum_map_range
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_sum_map_range
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
namespace ClauseBound.Inst.Half
theorem _root_.solution {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) :
    (labs (allTab (4 * h)) tr h s).length = bif tr then Rcol h s else Rrow h s := by
  have h1 : (labs (allTab (4 * h)) tr h s).length = ∑ j ∈ range (2 * h + 1), pz (wOf tr h s j) := by
    rw [labs, List.length_flatMap, ← sum_map_range]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj' : j ≤ 2 * h := by have := List.mem_range.1 hj; omega
    rw [pz]
    split_ifs with hw
    · rw [List.length_map, length_allTab_getD (toNat_wOf_le hs tr hj')]
    · rfl
  rw [h1]
  cases tr <;> rfl
end ClauseBound.Inst.Half
