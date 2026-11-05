-- Prove2me | solution 1 for ClauseBound.Inst.Half.mem_flatten_allTab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:44:18.503221+00:00
-- url     : https://prove2.me/submissions/e965b56b-7369-4ddc-9c96-d0745f585d2b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_foldl_roundT
import Theorems.Thm_ClauseBound_Part_ListP_le_sum_of_mem
import Theorems.Thm_ClauseBound_Part_mem_partsLe
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {W : ℕ} {L : List ℕ} :
    L ∈ (allTab W).flatten ↔ L.sum ≤ W ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by
  rw [allTab, foldl_roundT, tabK, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hL⟩
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hs, hp, hw⟩ := (mem_partsLe E W L).1 hL
    have := List.mem_range.1 hE
    exact ⟨by omega, fun n hn => (hp n hn).1, hw⟩
  · rintro ⟨hs, hp, hw⟩
    exact ⟨partsLe L.sum W, List.mem_map.2 ⟨L.sum, List.mem_range.2 (by omega), rfl⟩,
      (mem_partsLe _ _ _).2 ⟨rfl, fun n hn => ⟨hp n hn, (ListP.le_sum_of_mem hn).trans hs⟩, hw⟩⟩
end ClauseBound.Inst.Half
