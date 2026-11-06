-- Prove2me | solution 1 for Exits.length_tested_visits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:27:58.918802+00:00
-- url     : https://prove2.me/submissions/43860a9e-2e39-462b-9aee-aecaae942749

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
import Theorems.Thm_Exits_any_filterMap_sel
import Theorems.Thm_Exits_tested_append_of_fail
import Theorems.Thm_Exits_tested_append_of_pass
import Theorems.Thm_Exits_tested_cons_of_fail
import Theorems.Thm_Exits_tested_singleton
import Theorems.Thm_Groundwork_Stepped_filterMap_visits
import Theorems.Thm_Groundwork_Stepped_length_visits
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
theorem _root_.solution (step : ν → Option (ν × ν)) (v : ν → Bool) (w : List ν → Bool) (hw : ∀ st, w st = ((walkSel step st).map v).getD false) (k : ℕ) (s : ν) (r : List ν)
    (hk : ∀ x ∈ leaves step k s, step x = none) : (tested w (visits step k s r)).length + 1 ≤ 2 * (tested v (leaves step k s)).length + k := by
  induction k generalizing s r with
  | zero =>
    rw [show visits step 0 s r = [s :: r] from rfl, show leaves step 0 s = [s] from rfl, tested_singleton, tested_singleton]
    exact le_rfl
  | succ k ih =>
    cases h0 : step s with
    | none =>
      rw [show visits step (k + 1) s r = [s :: r] by simp [visits, h0], show leaves step (k + 1) s = [s] by simp [leaves, h0], tested_singleton, tested_singleton]
      simp only [List.length_singleton]; omega
    | some lh =>
      obtain ⟨l, h'⟩ := lh
      have ev : visits step (k + 1) s r = (s :: r) :: (visits step k l (h' :: r) ++ visits step k h' r) := by simp [visits, h0]
      have el : leaves step (k + 1) s = leaves step k l ++ leaves step k h' := by simp [leaves, h0]
      rw [el] at hk
      have hl : ∀ x ∈ leaves step k l, step x = none := fun x hx => hk x (List.mem_append_left _ hx)
      have hs : w (s :: r) = false := by rw [hw]; simp [walkSel, h0]
      have ha : (visits step k l (h' :: r)).any w = (leaves step k l).any v := by rw [← any_filterMap_sel (walkSel step) v w hw, filterMap_visits step k l (h' :: r) hl]
      have i1 := ih l (h' :: r) hl
      have i2 := ih h' r fun x hx => hk x (List.mem_append_right _ hx)
      have n1 := length_visits step k l (h' :: r)
      rw [ev, el, tested_cons_of_fail hs, List.length_cons]
      cases hp : (leaves step k l).any v with
      | true => rw [tested_append_of_pass (ha.trans hp), tested_append_of_pass hp]; omega
      | false => rw [tested_append_of_fail (ha.trans hp), tested_append_of_fail hp, List.length_append, List.length_append]; omega
end Exits
