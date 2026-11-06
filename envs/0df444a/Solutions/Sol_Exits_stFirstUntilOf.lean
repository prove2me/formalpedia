-- Prove2me | solution 1 for Exits.stFirstUntilOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:04.571592+00:00
-- url     : https://prove2.me/submissions/9a3c32ef-688a-4c80-bb43-73682872be0a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
import Theorems.Thm_Exits_foldl_first_tested
import Theorems.Thm_Exits_met_first
import Theorems.Thm_Exits_reach_le
import Theorems.Thm_Exits_tested_range
import Theorems.Thm_Groundwork_Stepped_foldl_first
import Theorems.Thm_Groundwork_Stepped_orbit_range
import Theorems.Thm_Groundwork_Stepped_sum_map_range
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
theorem _root_.solution : StFirstUntilOf := by
  intro H α β _ N M p a t v Sm hM
  have ho := orbit_range N a (N a) 0 (by omega)
  rw [← List.range_eq_range'] at ho
  have hmet : met (fun c (x : α × ℕ) => rangeG (firstG p) c x (v x.2)) Option.isSome none ((List.range (N a)).map fun y => (a, y))
      = (List.range (reach (fun y => p (v y)) (N a))).map fun y => (a, y) := by rw [← tested_range]; exact met_first p v a _
  have hr := reach_le (fun y => p (v y)) (N a)
  have key := H α β (Option ℕ) (α × ℕ) (rangeStart N) (rangeNext N) M (rangeG (firstG p)) Option.isSome noneC a _ ho (fun x => t x.2) (fun x => v x.2) (size a + size (N a)) (size (N a) + 1) Sm
  rw [show noneC a = none from rfl, hmet] at key
  have key2 := key
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM y (List.mem_range.1 hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := Nat.size_le_size ((List.mem_range.1 hy).le.trans hr)
      simp only [size_prod, size_nat]; omega)
    (by
      intro l hl
      rw [List.prefix_iff_eq_take] at hl
      rw [hl, ← List.map_take, List.take_range, List.foldl_map]
      rw [show List.foldl (fun c y => rangeG (firstG p) c (a, y) (v y)) none (List.range (min l.length (reach (fun y => p (v y)) (N a))))
        = (List.range (min l.length (reach (fun y => p (v y)) (N a)))).find? fun y => p (v y) from foldl_first (fun y => p (v y)) _]
      cases h : (List.range (min l.length (reach (fun y => p (v y)) (N a)))).find? fun y => p (v y) with
      | none => simp only [size_none]; omega
      | some i =>
        have hi := List.mem_range.1 (List.mem_of_find?_eq_some h)
        have := Nat.size_le_size (hi.le.trans ((min_le_right _ _).trans hr))
        simp only [size_some, size_nat]; omega)
  rw [List.map_map, List.foldl_map] at key2
  rw [← sum_map_range, ← foldl_first_tested p v, tested_range]
  exact key2
end Exits
