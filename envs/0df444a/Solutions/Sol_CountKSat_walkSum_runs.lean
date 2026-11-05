-- Prove2me | solution 1 for CountKSat.walkSum_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:16:13.813974+00:00
-- url     : https://prove2.me/submissions/aad0c285-4596-4b6f-a504-df929deb6011

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Poly_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_Walk
import Theorems.Thm_CountKSat_Walk_foldl_add_sel
import Theorems.Thm_CountKSat_Walk_sum_prefix_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_exists_round_of_orbit
import Theorems.Thm_Groundwork_Stepped_filterMap_visits
import Theorems.Thm_Groundwork_Stepped_foldWhile_runs
import Theorems.Thm_Groundwork_Stepped_guard_runs_none
import Theorems.Thm_Groundwork_Stepped_guard_runs_some
import Theorems.Thm_Groundwork_Stepped_length_visits
import Theorems.Thm_Groundwork_Stepped_orbit_visits
import Theorems.Thm_Groundwork_Stepped_sum_sel
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Stepped Groundwork.Sparsify
variable {α ν : Type}
open Walk
namespace CountKSat
theorem _root_.solution [HasSize ν] (step : ν → Option (ν × ν)) {root : α → ν} {T : Stepped ν ℕ} (d : ℕ) (a : α)
    (hd : ∀ x ∈ leaves step d (root a), step x = none) (v : ν → ℕ) (t Sm Sx B : ℕ)
    (hT : ∀ x ∈ leaves step d (root a), T.Runs x t Sm (v x))
    (hS : ∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx)
    (hB : ((leaves step d (root a)).map v).sum < 2 ^ B) :
    (walkSum step root T).Runs a ((leaves step d (root a)).length * (t + 2)) (Sx + (B + 1 + (Sm + 1)) + 1)
      ((leaves step d (root a)).map v).sum := by
  have ho : Orbit (walkNext step) (some [root a]) (visits step d (root a) [] ++ [[]]) :=
    orbit_visits step d (root a) [] [[]] hd (.cons .nil)
  have hf : (visits step d (root a) [] ++ [[]]).filterMap (walkSel step) = leaves step d (root a) := by
    rw [List.filterMap_append, filterMap_visits step d (root a) [] hd]
    simp [walkSel]
  have hlen : (visits step d (root a) [] ++ [[]]).length = 2 * (leaves step d (root a)).length := by
    rw [List.length_append, ← length_visits step d (root a) []]
    rfl
  have key := foldWhile_runs (start := fun a : α => some [root a]) (M := guard (walkSel step) T 0)
    (g := fun c _ b => c + b) (c₀ := fun _ => 0) (a := a) ho
    (fun st => ((walkSel step st).map fun _ => t).getD 0) (fun st => ((walkSel step st).map v).getD 0)
    Sx (B + 1) (Sm + 1)
    (by
      intro st hst
      cases h : walkSel step st with
      | none => exact (guard_runs_none h).mono le_rfl (by omega)
      | some x => exact guard_runs_some h (hT x (hf ▸ List.mem_filterMap.2 ⟨st, hst, h⟩)))
    (by
      intro st hst
      obtain ⟨i, rfl⟩ := exists_round_of_orbit step ho st hst
      exact hS i)
    (by
      intro l hl
      rw [foldl_add_sel, Nat.zero_add]
      have h1 := sum_prefix_le (walkSel step) v hl
      rw [hf] at h1
      exact Nat.succ_le_succ (Nat.size_le.2 (lt_of_le_of_lt h1 hB)))
  rw [sum_sel, foldl_add_sel, hf, hlen, Nat.zero_add] at key
  exact key.mono (le_of_eq (by ring)) le_rfl
end CountKSat
