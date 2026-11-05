-- Prove2me | solution 1 for ClauseBound.Inst.Half.len_state_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:50:52.259543+00:00
-- url     : https://prove2.me/submissions/77c75f38-8b1b-4daf-ad93-88203b2dcdf8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_len_map_partsLe_le
import Theorems.Thm_ClauseBound_Part_p_pos
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution (W k j : ℕ) (hj : j ≤ W + 1) :
    len ((List.range j).map fun E => partsLe E k) ≤ (7 * W + 10) * ∑ E ∈ range (W + 1), p E := by
  have h1 := len_map_partsLe_le W k j hj
  have h2 : ∑ E ∈ range j, p E ≤ ∑ E ∈ range (W + 1), p E :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hj)
  have h3 : 1 ≤ ∑ E ∈ range (W + 1), p E := by
    rw [Finset.sum_range_succ']
    have := p_pos 0
    omega
  have h4 : (7 * W + 8) * ∑ E ∈ range j, p E ≤ (7 * W + 8) * ∑ E ∈ range (W + 1), p E := Nat.mul_le_mul_left _ h2
  have h5 : (7 * W + 10) * ∑ E ∈ range (W + 1), p E = (7 * W + 8) * ∑ E ∈ range (W + 1), p E + 2 * ∑ E ∈ range (W + 1), p E := by ring
  omega
end ClauseBound.Inst.Half
