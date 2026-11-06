-- Prove2me | solution 1 for FreeCode.bruteCore_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:38:53.164768+00:00
-- url     : https://prove2.me/submissions/a643a2fb-68ec-45a5-993a-3dd2d2a085cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Basic
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic
import Definitions.Def_FreeCode_Brute
import Theorems.Thm_FreeCode_sum_satAt_pos
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapOut_runs
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
import Theorems.Thm_Groundwork_Stepped_sumRange_runs
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
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
namespace FreeCode
theorem _root_.solution {n : ℕ} (φ : Sat3.CNF n) : ∃ b : Bool,
    bruteCore.Runs (List.replicate n (), Decode.toN φ) (2 * 2 ^ n) (2 * size ((List.replicate n (), Decode.toN φ) : List Unit × Fml) + 3 * n + 12) b ∧
      (b = true ↔ Sat3.Satisfiable φ) := by
  obtain ⟨a, ha⟩ : ∃ a : List Unit × Fml, a = (List.replicate n (), Decode.toN φ) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : (List Unit × Fml) × ℕ → ℤ, f = fun q => ((PaddedDescent.satAt q.1.2 q.2).toNat : ℤ) := ⟨_, rfl⟩
  have hN : 2 ^ a.1.length = 2 ^ n := by rw [ha]; simp
  have hv : ∀ y, f (a, y) = ((PaddedDescent.satAt (Decode.toN φ) y).toNat : ℤ) := fun y => by rw [hf, ha]
  have hv1 : ∀ y, (f (a, y)).natAbs ≤ 1 := fun y => by rw [hv]; cases PaddedDescent.satAt (Decode.toN φ) y <;> simp
  have hs2 : size (2 ^ n) = n + 2 := by rw [size_nat, Nat.size_pow]
  have hM : ∀ y < (fun p : List Unit × Fml => 2 ^ p.1.length) a, (Stepped.ofFun f).Runs (a, y) 1 (size a + n + 3) (f (a, y)) := by
    intro y hy
    have hy' : y < 2 ^ n := hN ▸ hy
    refine (Stepped.ofFun_runs f (a, y)).mono le_rfl ?_
    have s1 : size y ≤ n + 1 := by rw [size_nat]; exact Nat.succ_le_succ (Nat.size_le.2 hy')
    have s2 : size (f (a, y)) ≤ 2 := by
      rw [size_int]
      have : (f (a, y)).natAbs.size ≤ 1 := Nat.size_le.2 (by have := hv1 y; omega)
      omega
    have s3 : size (a, y) = size a + size y := rfl
    rw [s3]
    omega
  have hr := Stepped.mapOut_runs (f := fun v : ℤ => decide (0 < v)) (Stepped.sumRange_runs (N := fun p : List Unit × Fml => 2 ^ p.1.length)
    (M := Stepped.ofFun f) (a := a) (fun _ => 1) (fun y => f (a, y)) 1 (size a + n + 3) hM fun y _ => hv1 y)
  rw [hN] at hr
  refine ⟨decide (0 < ∑ y ∈ Finset.range (2 ^ n), f (a, y)), ?_, ?_⟩
  · have hB : bruteCore = Stepped.mapOut (Stepped.sumRange (fun p : List Unit × Fml => 2 ^ p.1.length) (Stepped.ofFun f)) fun v => decide (0 < v) := by
      rw [hf]
      rfl
    rw [hB, ← ha]
    refine hr.mono ?_ ?_
    · simp [Finset.sum_const, Finset.card_range, mul_comm]
    · rw [mul_one, hs2]
      omega
  · rw [decide_eq_true_iff, ← sum_satAt_pos φ]
    simp only [hv]
end FreeCode
