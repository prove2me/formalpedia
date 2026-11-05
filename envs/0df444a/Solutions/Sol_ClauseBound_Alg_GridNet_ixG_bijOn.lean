-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.ixG_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:13:55.603093+00:00
-- url     : https://prove2.me/submissions/2209df34-fc2d-44c2-b504-18ee83406e93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_Groundwork_Grid_mixed_inj
import Theorems.Thm_Groundwork_Grid_mixed_lt
import Theorems.Thm_Groundwork_Grid_mixed_surj
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
import Theorems.Thm_Groundwork_tri_inj
import Theorems.Thm_Groundwork_tri_lt
import Theorems.Thm_Groundwork_tri_surj
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
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d : ℕ) : Set.BijOn (ixG p d) (Ω (Fin p) (Fin d)) (range (nRectG p d)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
    simp only [coe_range, Set.mem_Iio, ixG]
    exact mixed_lt (tri_lt (Fin.lt_def.1 h.1) b.2) (tri_lt (Fin.lt_def.1 h.2) i'.2)
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h ⟨⟨a₂, b₂⟩, ⟨i₂, i₂'⟩⟩ h₂ heq
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h h₂
    simp only [ixG] at heq
    obtain ⟨e1, e2⟩ := mixed_inj (n := c2 d) (tri_lt (Fin.lt_def.1 h.2) i'.2) (tri_lt (Fin.lt_def.1 h₂.2) i₂'.2) heq
    obtain ⟨e3, e4⟩ := tri_inj (Fin.lt_def.1 h.1) (Fin.lt_def.1 h₂.1) e1
    obtain ⟨e5, e6⟩ := tri_inj (Fin.lt_def.1 h.2) (Fin.lt_def.1 h₂.2) e2
    rw [Fin.ext e3, Fin.ext e4, Fin.ext e5, Fin.ext e6]
  · intro z hz
    simp only [coe_range, Set.mem_Iio] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mixed_surj hz
    obtain ⟨a, b, hab, hb, rfl⟩ := tri_surj (K := p) hx
    obtain ⟨i, i', hii, hi', rfl⟩ := tri_surj (K := d) hy
    refine ⟨((⟨a, by omega⟩, ⟨b, hb⟩), (⟨i, by omega⟩, ⟨i', hi'⟩)), ?_, rfl⟩
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Fin.lt_def]
    exact ⟨hab, hii⟩
end ClauseBound.Alg.GridNet
