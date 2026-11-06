-- Prove2me | solution 1 for Exits.stWalkUntilOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:33:33.691196+00:00
-- url     : https://prove2.me/submissions/df4b3470-ff67-49a8-a63b-4e30e64ff959

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
import Theorems.Thm_Exits_length_tested_visits
import Theorems.Thm_Exits_any_filterMap_sel
import Theorems.Thm_Exits_any_tested
import Theorems.Thm_Exits_filterMap_tested
import Theorems.Thm_Exits_foldl_or
import Theorems.Thm_Exits_mem_of_mem_tested
import Theorems.Thm_Exits_met_or
import Theorems.Thm_Exits_tested_append_of_fail
import Theorems.Thm_Exits_tested_append_of_pass
import Theorems.Thm_Exits_tested_of_fail
import Theorems.Thm_Exits_tested_singleton
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_exists_round_of_orbit
import Theorems.Thm_Groundwork_Stepped_filterMap_visits
import Theorems.Thm_Groundwork_Stepped_guard_runs_none
import Theorems.Thm_Groundwork_Stepped_guard_runs_some
import Theorems.Thm_Groundwork_Stepped_length_visits
import Theorems.Thm_Groundwork_Stepped_orbit_visits
import Theorems.Thm_Groundwork_Stepped_sum_sel
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
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
section
open Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β γ τ ν : Type}
namespace Exits
theorem _root_.solution : StWalkUntilOf := by
  intro H α ν _ step root T k a hk v t Sm Sx hT hS
  obtain ⟨w, hw⟩ : ∃ w : List ν → Bool, ∀ st, w st = ((walkSel step st).map v).getD false := ⟨_, fun _ => rfl⟩
  have ho : Orbit (walkNext step) (some [root a]) (visits step k (root a) [] ++ [[]]) := orbit_visits step k (root a) [] [[]] hk (.cons .nil)
  have hf : (visits step k (root a) [] ++ [[]]).filterMap (walkSel step) = leaves step k (root a) := by
    rw [List.filterMap_append, filterMap_visits step k (root a) [] hk]
    simp [walkSel]
  have hfm : (tested w (visits step k (root a) [] ++ [[]])).filterMap (walkSel step) = tested v (leaves step k (root a)) := by rw [filterMap_tested (walkSel step) v w hw, hf]
  have hlen : (tested w (visits step k (root a) [] ++ [[]])).length ≤ 2 * (tested v (leaves step k (root a))).length + k := by
    have ha : (visits step k (root a) []).any w = (leaves step k (root a)).any v := by rw [← any_filterMap_sel (walkSel step) v w hw, filterMap_visits step k (root a) [] hk]
    cases hp : (leaves step k (root a)).any v with
    | true =>
      have := length_tested_visits step v w hw k (root a) [] hk
      rw [tested_append_of_pass (ha.trans hp)]; omega
    | false =>
      have := length_visits step k (root a) []
      rw [tested_append_of_fail (ha.trans hp), tested_of_fail hp, tested_singleton, List.length_append, List.length_singleton]; omega
  have key := H α Bool Bool (List ν) (fun a : α => some [root a]) (walkNext step) (guard (walkSel step) T false) (fun c _ b => c || b) id (fun _ => false) a _ ho
    (fun st => ((walkSel step st).map fun _ => t).getD 0) w Sx 1 (Sm + 1)
  rw [met_or w] at key
  have key2 := key
    (by
      intro st hst
      rw [hw st]
      cases h : walkSel step st with
      | none => exact (guard_runs_none h).mono le_rfl (by omega)
      | some x => exact guard_runs_some h (hT x (hfm ▸ List.mem_filterMap.2 ⟨st, hst, h⟩)))
    (by
      intro st hst
      obtain ⟨i, rfl⟩ := exists_round_of_orbit step ho st (mem_of_mem_tested hst)
      exact hS i)
    (fun _ _ => le_rfl)
  rw [sum_sel, foldl_or, hfm, Bool.false_or, any_tested, ← any_filterMap_sel (walkSel step) v w hw, hf] at key2
  exact key2.mono (by rw [Nat.mul_add]; omega) le_rfl
end Exits
