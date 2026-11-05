-- Prove2me | solution 1 for CountKSat.Walk.sum_prefix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:09:52.948228+00:00
-- url     : https://prove2.me/submissions/31b58750-b3b2-418f-84f8-51ef7d386f91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Poly_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Stepped Groundwork.Sparsify
variable {α ν : Type}
open CountKSat.Walk
variable {τ : Type}
namespace CountKSat.Walk
theorem _root_.solution (sel : τ → Option ν) (v : ν → ℕ) {l xs : List τ} (h : l <+: xs) :
    ((l.filterMap sel).map v).sum ≤ ((xs.filterMap sel).map v).sum := by
  obtain ⟨r, rfl⟩ := h
  rw [List.filterMap_append, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _
end CountKSat.Walk
