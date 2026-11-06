-- Prove2me | solution 1 for Coding.restr_padOcc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:02:58.167878+00:00
-- url     : https://prove2.me/submissions/b2a23f0f-c1d8-4b6f-919b-b48a264dffe9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Coding_getD_padOcc_occ
import Theorems.Thm_Coding_map_links
import Theorems.Thm_Coding_mem_occOf_iff
import Theorems.Thm_Coding_mem_testsBetween
import Theorems.Thm_Coding_mem_tests_iff
import Theorems.Thm_Coding_testsBetween_comm
import Theorems.Thm_Eight_ViaGrouping_restr_of_gt
import Theorems.Thm_Eight_ViaGrouping_restr_of_lt
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_Groundwork_TM_update_withIO
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : Fin g} (hab : a ≠ b) (z : List Bool) : restr g 3 Φ a.val b.val (padOcc g Φ a z) = restrict g Φ a.val b.val z := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · have e := map_links hg h3 h.le (Φ := Φ) fun q => (padOcc g Φ a z).getD (q.1 - a.val * (mu g Φ * 3)) false
    simp only [Nat.add_sub_cancel_left] at e
    rw [restr_of_lt h, e, restrict]
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨ht, c1, -⟩ := (mem_testsBetween h3 h.le).1 hp
    obtain ⟨ho, -, -⟩ := (mem_tests_iff h3 (o := p.1) (o' := p.2)).1 ht
    rw [if_pos c1, getD_padOcc_occ h3 a z ((mem_occOf_iff hg).2 ⟨ho, c1⟩)]
  · have e := map_links hg h3 h.le (Φ := Φ) fun q => (padOcc g Φ a z).getD (q.2 - a.val * (mu g Φ * 3)) false
    simp only [Nat.add_sub_cancel_left] at e
    rw [restr_of_gt h, e, restrict, testsBetween_comm a.val b.val]
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨ht, c1, c2⟩ := (mem_testsBetween h3 h.le).1 hp
    obtain ⟨-, ho', -⟩ := (mem_tests_iff h3 (o := p.1) (o' := p.2)).1 ht
    rw [if_neg (by omega), getD_padOcc_occ h3 a z ((mem_occOf_iff hg).2 ⟨ho', c2⟩)]
end Coding
