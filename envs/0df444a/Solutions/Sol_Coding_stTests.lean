-- Prove2me | solution 1 for Coding.stTests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:28:26.746473+00:00
-- url     : https://prove2.me/submissions/78715c71-bd95-4270-b98d-fe23a4dbf85a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Coding_occOfSlot_injective
import Theorems.Thm_Coding_exists_occOfSlot
import Theorems.Thm_Coding_nodup_tests
import Theorems.Thm_Coding_toFinset_tests
import Theorems.Thm_Coding_toFinset_occAll
import Theorems.Thm_Coding_toFinset_vars
import Theorems.Thm_Coding_length_occIn_le
import Theorems.Thm_Coding_mem_occAll
import Theorems.Thm_Coding_nodup_occIn
import Theorems.Thm_Eight_card_testsOf_add
import Theorems.Thm_Eight_card_tests_at_le_two
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}
namespace Coding
theorem _root_.solution : StTests := by
  intro Φ hΦ hC
  have h3 : ∀ C ∈ Φ, C.length ≤ 3 := fun C h => (hC C h).2
  have inj2 : Function.Injective fun t : Slot 1 Φ.length 3 × Slot 1 Φ.length 3 => (occOfSlot t.1, occOfSlot t.2) := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    rw [occOfSlot_injective h.1, occOfSlot_injective h.2]
  have hnd : (occAll Φ).Nodup := nodup_occIn h3 0 Φ.length
  have hsum : (tests Φ).length + ((occAll Φ).map fun o => (litOf Φ o).1).toFinset.card = (occAll Φ).length := by
    rw [← List.toFinset_card_of_nodup (nodup_tests h3), toFinset_tests h3, card_image_of_injective _ inj2, toFinset_vars,
      ← List.toFinset_card_of_nodup hnd, toFinset_occAll h3, card_image_of_injective _ occOfSlot_injective]
    exact card_testsOf_add h3 (by omega)
  refine ⟨fun o ho => ?_, hsum, ?_⟩
  · obtain ⟨p₀, rfl⟩ := exists_occOfSlot h3 ho
    rw [← List.toFinset_card_of_nodup ((nodup_tests h3).filter _)]
    refine (card_le_card (t := ({t ∈ testsOf Φ 1 Φ.length 3 | t.1 = p₀ ∨ t.2 = p₀} : Finset _).image fun t => (occOfSlot t.1, occOfSlot t.2)) ?_).trans (card_image_le.trans (card_tests_at_le_two p₀))
    intro x hx
    rw [List.mem_toFinset, List.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx3 := List.mem_toFinset.2 hx1
    rw [toFinset_tests h3] at hx3
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hx3
    simp only [Bool.or_eq_true, beq_iff_eq] at hx2
    exact mem_image.2 ⟨t, mem_filter.2 ⟨ht, hx2.imp (fun h => occOfSlot_injective h) fun h => occOfSlot_injective h⟩, rfl⟩
  · have h1 := length_occIn_le h3 0 Φ.length
    have h2 : 0 < ((occAll Φ).map fun o => (litOf Φ o).1).toFinset.card := by
      obtain ⟨C, Φ', rfl⟩ := List.exists_cons_of_ne_nil hΦ
      have h0 : ((0, 0) : ℕ × ℕ) ∈ occAll (C :: Φ') := mem_occAll.2 (List.length_pos_iff.2 (hC C List.mem_cons_self).1)
      exact card_pos.2 ⟨_, List.mem_toFinset.2 (List.mem_map_of_mem h0)⟩
    have h4 : (occAll Φ).length ≤ 3 * Φ.length := h1
    omega
end Coding
