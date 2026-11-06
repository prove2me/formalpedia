-- Prove2me | solution 1 for Coding.links_eq_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:24.921895+00:00
-- url     : https://prove2.me/submissions/83b9bc22-94af-4e24-b00b-54c6855c4f19

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Coding_clusterOf_eq_iff
import Theorems.Thm_Coding_mem_testsBetween
import Theorems.Thm_Coding_pairwise_tests
import Theorems.Thm_Coding_eq_of_lex
import Theorems.Thm_Coding_linkB_iff_places
import Theorems.Thm_Coding_mem_occAll_of_varAt
import Theorems.Thm_Coding_mem_tests_iff
import Theorems.Thm_Coding_pairwise_product
import Theorems.Thm_Coding_place_div_mod
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Count_locals_eq
import Theorems.Thm_Groundwork_Prog_Count_mem_links
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
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) :
    (links g 3 Φ a b).map (fun p => (a * (mu g Φ * 3) + p.1, b * (mu g Φ * 3) + p.2)) = (testsBetween g Φ a b).map fun p => (place p.1, place p.2) := by
  refine eq_of_lex ?_ ?_ fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · rw [List.pairwise_map, links, locals_eq hg]
    refine ((pairwise_product List.pairwise_lt_range List.pairwise_lt_range).filter _).imp ?_
    rintro p q (h | ⟨h1, h2⟩)
    · exact Or.inl (Nat.add_lt_add_left h _)
    · exact Or.inr ⟨congrArg (a * (mu g Φ * 3) + ·) h1, Nat.add_lt_add_left h2 _⟩
  · exact (pairwise_tests h3).sublist (List.filter_sublist.map _)
  · obtain ⟨⟨r, r'⟩, hp, rfl⟩ := List.mem_map.1 hq
    have hp' := (mem_links hg a b (r, r')).1 hp
    have hr : r < mu g Φ * 3 := hp'.1
    have hr' : r' < mu g Φ * 3 := hp'.2.1
    have hl : linkB 3 Φ (a * (mu g Φ * 3) + r) (b * (mu g Φ * 3) + r') = true := hp'.2.2
    obtain ⟨-, hs, hv, -⟩ := (linkB_iff_places _ _).1 hl
    obtain ⟨v, hv1⟩ := Option.isSome_iff_exists.1 hs
    have ho := mem_occAll_of_varAt hv1
    have ho' := mem_occAll_of_varAt (hv.symm.trans hv1)
    refine List.mem_map.2 ⟨(((a * (mu g Φ * 3) + r) / 3, (a * (mu g Φ * 3) + r) % 3), ((b * (mu g Φ * 3) + r') / 3, (b * (mu g Φ * 3) + r') % 3)), (mem_testsBetween h3 hab).2 ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (mem_tests_iff h3).2 ⟨ho, ho', by rw [place_div_mod, place_div_mod]; exact hl⟩
    · refine (clusterOf_eq_iff hg h3 ho a).2 ?_
      rw [place_div_mod]
      omega
    · refine (clusterOf_eq_iff hg h3 ho' b).2 ?_
      rw [place_div_mod]
      omega
    · simp only [place_div_mod]
  · obtain ⟨⟨o, o'⟩, hp, rfl⟩ := List.mem_map.1 hq
    obtain ⟨ht, h1, h2⟩ := (mem_testsBetween h3 hab).1 hp
    obtain ⟨ho, ho', hl⟩ := (mem_tests_iff h3).1 ht
    obtain ⟨c1, c2⟩ := (clusterOf_eq_iff hg h3 ho a).1 h1
    obtain ⟨c3, c4⟩ := (clusterOf_eq_iff hg h3 ho' b).1 h2
    refine List.mem_map.2 ⟨(place o - a * (mu g Φ * 3), place o' - b * (mu g Φ * 3)), (mem_links hg a b _).2 ⟨?_, ?_, ?_⟩, ?_⟩
    · change place o - a * (mu g Φ * 3) < mu g Φ * 3
      omega
    · change place o' - b * (mu g Φ * 3) < mu g Φ * 3
      omega
    · change linkB 3 Φ (a * (mu g Φ * 3) + (place o - a * (mu g Φ * 3))) (b * (mu g Φ * 3) + (place o' - b * (mu g Φ * 3))) = true
      rw [Nat.add_sub_cancel' c1, Nat.add_sub_cancel' c3]
      exact hl
    · change (a * (mu g Φ * 3) + (place o - a * (mu g Φ * 3)), b * (mu g Φ * 3) + (place o' - b * (mu g Φ * 3))) = (place o, place o')
      rw [Nat.add_sub_cancel' c1, Nat.add_sub_cancel' c3]
end Coding
