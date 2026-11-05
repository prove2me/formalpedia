-- Prove2me | solution 1 for ClauseBound.Inst.Half.sum_map_labs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:36:34.768046+00:00
-- url     : https://prove2.me/submissions/3178bfca-e62e-47a6-8c21-3a4a27ee8f03

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_ClauseBound_Inst_Half_Labs_sum_map_range_int
import Theorems.Thm_ClauseBound_Inst_Half_Labs_sum_map_flatMap
import Theorems.Thm_ClauseBound_Inst_Half_toNat_wOf_le
import Theorems.Thm_ClauseBound_Boson_Dual_sum_map_flatMap
import Theorems.Thm_ClauseBound_Inst_Half_nodup_map_coe_allTab_getD
import Theorems.Thm_ClauseBound_Inst_Half_toFinset_map_coe_allTab_getD
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
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
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
namespace ClauseBound.Inst.Half
theorem _root_.solution {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) (G : ℕ → Multiset ℕ → ℤ) :
    ((labs (allTab (4 * h)) tr h s).map fun p => G p.1 (p.2 : Multiset ℕ)).sum
      = ∑ j ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (wOf tr h s j), G j τ := by
  rw [labs, sum_map_flatMap, ← sum_map_range_int]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hj' : j ≤ 2 * h := by have := List.mem_range.1 hj; omega
  rw [ClauseBound.Boson.Pz]
  split_ifs with hw
  · have hW := toNat_wOf_le hs tr hj'
    rw [← toFinset_map_coe_allTab_getD hW, List.sum_toFinset _ (nodup_map_coe_allTab_getD hW), List.map_map, List.map_map]
    rfl
  · simp
end ClauseBound.Inst.Half
