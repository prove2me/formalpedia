-- Prove2me | solution 1 for Coding.stWrites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:44.764237+00:00
-- url     : https://prove2.me/submissions/393a83a7-ac6a-44ff-a63b-f436d757090a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Sets
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_map
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
open Finset
namespace Coding
theorem _root_.solution : StWrites := by
  intro n Φ
  constructor
  · have e : (Φ.clauses.toList.map Finset.toList).map List.toFinset = Φ.clauses.toList := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id Φ.clauses.toList]
      exact List.map_congr_left fun E _ => Finset.toList_toFinset E
    refine ⟨Φ.clauses.toList.map Finset.toList, ?_, ?_, ?_⟩
    · intro C hC
      obtain ⟨E, -, rfl⟩ := List.mem_map.1 hC
      exact Finset.nodup_toList E
    · rw [e]; exact Finset.nodup_toList _
    · rw [e]; exact Finset.toList_toFinset _
  · rintro φ ⟨h1, h2, h3⟩
    have hmem : ∀ C ∈ φ, C.toFinset ∈ Φ.clauses := fun C hC => h3 ▸ List.mem_toFinset.2 (List.mem_map_of_mem hC)
    refine ⟨⟨fun C hC => ?_, List.Nodup.of_map _ h2⟩, ?_, fun hnil => ?_, ?_, ?_⟩
    · rw [← List.toFinset_card_of_nodup (h1 C hC)]
      exact Φ.width _ (hmem C hC)
    · rw [← h3, List.toFinset_card_of_nodup h2, List.length_map]
    · simpa using Φ.nonempty _ (hmem [] hnil)
    · rintro ⟨a, ha⟩
      refine ⟨a, fun E hE => ?_⟩
      rw [← h3, List.mem_toFinset] at hE
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hE
      obtain ⟨l, hl, h⟩ := ha C hC
      exact ⟨l, List.mem_toFinset.2 hl, h⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, fun C hC => ?_⟩
      obtain ⟨l, hl, h⟩ := ha _ (hmem C hC)
      exact ⟨l, List.mem_toFinset.1 hl, h⟩
end Coding
