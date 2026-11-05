-- Prove2me | solution 1 for Eight.Fact.sum_words_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:44.702343+00:00
-- url     : https://prove2.me/submissions/e89604b8-f73d-42b6-ae52-c01b4a99bdd5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Eight_Fact_card_filter_range
import Theorems.Thm_Eight_Fact_eq_map_getD
import Theorems.Thm_Eight_Fact_getD_map_range
import Theorems.Thm_Eight_Fact_countP_getD
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
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
import Theorems.Thm_Groundwork_Unary_comp
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
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.map
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
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact
namespace Eight.Fact
theorem _root_.solution (t i : ℕ) (g : ℕ → Bool → ℤ) :
    ∑ Q ∈ words t, (if Q.count true = i then ∏ s ∈ range t, g s (Q.getD s false) else 0) =
      ∑ S ∈ (range t).powersetCard i, ∏ s ∈ range t, g s (decide (s ∈ S)) := by
  rw [← sum_filter]
  refine sum_nbij' (fun Q => (range t).filter fun s => Q.getD s false = true) (fun S => (List.range t).map fun s => decide (s ∈ S)) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    rw [mem_filter, mem_words] at hQ
    rw [mem_powersetCard]
    exact ⟨filter_subset _ _, by rw [card_filter_range, countP_getD hQ.1, hQ.2]⟩
  · intro S hS
    rw [mem_powersetCard] at hS
    rw [mem_filter, mem_words]
    refine ⟨by simp, ?_⟩
    rw [List.count, List.countP_map, ← hS.2, ← card_filter_range]
    congr 1
    ext s
    simp only [mem_filter, mem_range, Function.comp, beq_true, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_range.1 (hS.1 h), h⟩⟩
  · intro Q hQ
    rw [mem_filter, mem_words] at hQ
    obtain ⟨rfl, -⟩ := hQ
    conv_rhs => rw [eq_map_getD Q]
    refine List.map_congr_left fun s hs => ?_
    simp [List.mem_range.1 hs]
  · intro S hS
    rw [mem_powersetCard] at hS
    ext s
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      rw [getD_map_range h1] at h2
      simpa using h2
    · intro h
      have h1 := mem_range.1 (hS.1 h)
      exact ⟨h1, by rw [getD_map_range h1]; simpa using h⟩
  · intro Q _
    refine prod_congr rfl fun s hs => ?_
    congr 1
    simp [mem_range.1 hs]
end Eight.Fact
