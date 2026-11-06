-- Prove2me | solution 1 for Eight.color_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:38:25.664084+00:00
-- url     : https://prove2.me/submissions/099600ae-8f19-4636-ba42-8343eb021612

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblemsStatement
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_Eight_Cor_Defs
import Definitions.Def_Eight_Level_End
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_KSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_WidthK_Top_EndLemmas
import Definitions.Def_WidthK_Decode
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Sized
import Definitions.Def_GraphProblems_ColorTM
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_CountKSat_Walk
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_WidthK_Top_Sat
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Graph
import Theorems.Thm_CountKSat_EndLemmas_CountsTM_mono
import Theorems.Thm_GraphProblems_cntN_dedup
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Paper_Achievable_mono
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.dedup
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
open Eight
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing
namespace Eight
theorem _root_.solution (hR1 : StRead1) (hSh : StShapeColor) (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} {E : Stepped (List Unit × Fml) (List Bool)} {c : ℕ} (hc : Serves E (max k 2) (δ / k) c)
    (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ T : ℕ, (Stepped.mapIn (readC k) E).Runs (code G) T ((c * k ^ c + c) * (n + 2) ^ (c * k ^ c + c)) (SatK.binary (n * k) (cntN (n * k) (colorF k n (matrix G)))) ∧
      (T : ℝ) ≤ ((c * k ^ c + c : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨T, hr, hT⟩ := hc (n * k) (colorF k n (matrix G)).dedup (fun C hC => hSh k n (matrix G) C (List.mem_dedup.1 hC)) (List.nodup_dedup _)
  have hread : readC k (code G) = (List.replicate (n * k) (), (colorF k n (matrix G)).dedup) := by
    simp [readC, hR1 n G]
  rw [← hread] at hr
  have hrun := Stepped.mapIn_runs hr
  rw [cntN_dedup] at hrun
  have hc1 : c ≤ c * k ^ c := Nat.le_mul_of_pos_right c (Nat.pow_pos hk)
  refine ⟨T, hrun.mono le_rfl ?_, hT.trans ?_⟩
  · calc c * (n * k + 2) ^ c ≤ c * (k * (n + 2)) ^ c := by
          refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ c)
          nlinarith
      _ = c * k ^ c * (n + 2) ^ c := by rw [mul_pow, mul_assoc]
      _ ≤ (c * k ^ c + c) * (n + 2) ^ (c * k ^ c + c) :=
          Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
  · have e1 : δ / k * ((n * k : ℕ) : ℝ) = δ * n := by
      push_cast
      field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast hc1.trans (Nat.le_add_right _ _)
end Eight
