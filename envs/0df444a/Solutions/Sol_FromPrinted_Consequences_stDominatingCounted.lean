-- Prove2me | solution 1 for FromPrinted.Consequences.stDominatingCounted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:12:32.315101+00:00
-- url     : https://prove2.me/submissions/a577ebb3-0b21-487d-b596-e42574ef2eeb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_Consequences_Dom
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Dom
import Theorems.Thm_Consequences_cntS_le
import Theorems.Thm_Consequences_dom_size
import Theorems.Thm_Consequences_size_dnode_le
import Theorems.Thm_CountKSat_EndLemmas_CountsTM_mono
import Theorems.Thm_CountKSat_stWalkSum
import Theorems.Thm_Eight_ViaGrouping_Cost_floor_le
import Theorems.Thm_FromPrinted_Consequences_SIZED_counts
import Theorems.Thm_GraphProblems_stCertDom
import Theorems.Thm_GraphProblems_stCertRead
import Theorems.Thm_GraphProblems_stDom
import Theorems.Thm_GraphProblems_stRead2
import Theorems.Thm_GraphProblems_stShortens
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SplitCount_size_list_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
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
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open Consequences SplitCount
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper
namespace FromPrinted.Consequences
theorem _root_.solution : StDominatingCounted := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  -- «Choose w so large that the number of leaves is at most 2^{δn/2}»
  obtain ⟨w, -, hsh⟩ := stShortens (δ / 2) hδ2
  -- «apply Corollary 6 to each leaf»
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := SIZED_counts w hδ2
  refine ⟨w, ℓ, τ, 8 * w + 40 + c * 4 ^ c + c + 4, hsh, ?_, fun n G s hs => ?_⟩
  · have := IsPolyT.mapIn (M := SIZED w ℓ τ) stCertDom.2.2
    have := isPolyT_walkSum (T := Stepped.mapIn leafD (SIZED w ℓ τ)) (stCertDom.1 w) stCertDom.2.1
    exact ⟨IsPolyT.mapIn (M := walkSum (stepD w) rootD (Stepped.mapIn leafD (SIZED w ℓ τ))) stCertRead.2⟩
  obtain ⟨t1, t2, t3, t4⟩ := hsh n s (matrix G)
  obtain ⟨a, ha⟩ : ∃ a : List Unit × ℕ × List Bool, a = (List.replicate n (), s, matrix G) := ⟨_, rfl⟩
  rw [← ha] at t1 t2 t3 t4
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hleaf : ∀ x ∈ leaves (stepD w) (2 * n) (rootD a), (Stepped.mapIn leafD (SIZED w ℓ τ)).Runs x ⌊(c : ℝ) * E⌋₊ (c * (4 * X) ^ c) (cntS n s (leafD x).2.2) := by
    intro x hx
    obtain ⟨-, h1, h2, h3⟩ := t2 x hx
    obtain ⟨T, hr, hTle⟩ := hc n s (leafD x).2.2 hs h2
    have e : leafD x = (List.replicate n (), s, (leafD x).2.2) := by simp [leafD, h1]
    rw [← e] at hr
    exact (Stepped.mapIn_runs hr).mono (Nat.le_floor (hE ▸ hTle)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c))
  have hstack : ∀ i, size ((round (stepD w))^[i] ([rootD a], [])).1 ≤ (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 := by
    intro i
    obtain ⟨s1, s2⟩ := t4 i
    exact SplitCount.size_list_le s1 fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := s2 x hx
      exact hX ▸ size_dnode_le hs h1 h2 h3 h4 h5
  have hlt : ((leaves (stepD w) (2 * n) (rootD a)).map fun x => cntS n s (leafD x).2.2).sum < 2 ^ (n + 1) := by
    rw [← t3]
    exact lt_of_le_of_lt (cntS_le _ _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  -- «and add up»
  have wr := stWalkSum _ _ (stepD w) rootD (Stepped.mapIn leafD (SIZED w ℓ τ)) (2 * n) a (fun x hx => (t2 x hx).1)
    (fun x => cntS n s (leafD x).2.2) ⌊(c : ℝ) * E⌋₊ (c * (4 * X) ^ c) _ (n + 1) hleaf hstack hlt
  rw [← t3, stDom n G s] at wr
  have hread : read2 (codeWith G s) = a := by rw [stRead2 n G s, ha]
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (leaves (stepD w) (2 * n) (rootD a)).length := ⟨_, rfl⟩
  rw [← hL] at wr t1
  rw [← hread] at wr
  refine ⟨_, (Stepped.mapIn_runs wr).mono le_rfl (by rw [← hX]; exact dom_size hX), ?_⟩
  have hfl : ((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * E := Nat.floor_le (by positivity)
  have hLE : (L : ℝ) ≤ E := hE ▸ t1
  have hEE : E * E = (2 : ℝ) ^ (δ * n) := by
    rw [hE, ← Real.rpow_add two_pos]
    congr 1
    ring
  have hE0 : 0 ≤ E := by linarith
  have hcK : (c : ℝ) + 2 ≤ ((8 * w + 40 + c * 4 ^ c + c + 4 : ℕ) : ℝ) := by
    have : c + 2 ≤ 8 * w + 40 + c * 4 ^ c + c + 4 := by omega
    exact_mod_cast this
  calc ((L * (⌊(c : ℝ) * E⌋₊ + 2) : ℕ) : ℝ) = (L : ℝ) * (((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) + 2) := by push_cast; ring
    _ ≤ E * ((c : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE0
    _ = ((c : ℝ) + 2) * (E * E) := by ring
    _ = ((c : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := by rw [hEE]
    _ ≤ ((8 * w + 40 + c * 4 ^ c + c + 4 : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hcK (by positivity)
end FromPrinted.Consequences
