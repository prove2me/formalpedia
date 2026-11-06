-- Prove2me | solution 1 for Coding.exists_padOcc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:48:38.658603+00:00
-- url     : https://prove2.me/submissions/798bd1b7-56fa-468e-a913-8439a1a7c172

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Coding_length_padOcc
import Theorems.Thm_Coding_getD_padOcc
import Theorems.Thm_Coding_place_sub
import Theorems.Thm_Coding_getD_map_idxOf
import Theorems.Thm_Coding_litAt_local
import Theorems.Thm_Coding_ext_getD
import Theorems.Thm_Coding_mem_occIn
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Count_locals_eq
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) (a : Fin g) {y : List Bool} (hy : y.length = mu g Φ * 3)
    (h0 : ((locals g 3 Φ).all fun r => (litAt 3 Φ (a.val * (mu g Φ * 3) + r)).isSome || !(y.getD r false)) = true) :
    ∃ z : List Bool, z.length = (occOf g Φ a.val).length ∧ padOcc g Φ a z = y := by
  refine ⟨(occOf g Φ a.val).map fun o => y.getD (place o - a.val * (mu g Φ * 3)) false, List.length_map _, ext_getD ((length_padOcc a _).trans hy.symm) fun i hi => ?_⟩
  rw [length_padOcc] at hi
  rw [getD_padOcc a _ hi]
  by_cases h : i % 3 < (Φ.getD (a.val * mu g Φ + i / 3) []).length
  · have ho : (a.val * mu g Φ + i / 3, i % 3) ∈ occOf g Φ a.val := mem_occIn.2 ⟨Nat.le_add_right _ _, by change a.val * mu g Φ + i / 3 < _; omega, h⟩
    rw [decide_eq_true h, Bool.true_and, bitAt, getD_map_idxOf _ ho, place_sub (Nat.le_add_right _ _)]
    congr 1
    omega
  · rw [locals_eq hg, List.all_eq_true] at h0
    have h1 := h0 i (List.mem_range.2 hi)
    rw [litAt_local, if_neg h] at h1
    rw [decide_eq_false h, Bool.false_and]
    cases hb : y.getD i false with
    | false => rfl
    | true =>
      rw [hb] at h1
      exact absurd h1 (by decide)
end Coding
