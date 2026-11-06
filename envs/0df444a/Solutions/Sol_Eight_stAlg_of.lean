-- Prove2me | solution 1 for Eight.stAlg_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:09:07.646201+00:00
-- url     : https://prove2.me/submissions/04630376-efb2-44a5-8050-47e9ef972a55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundStatement
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
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
import Definitions.Def_CircuitLowerBound_Closed
import Definitions.Def_CircuitLowerBound_Inf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_ENP
import Theorems.Thm_CircuitLowerBound_Alg_exists_guess
import Theorems.Thm_CircuitLowerBound_Alg_outputs_unique
import Theorems.Thm_CircuitLowerBound_Alg_runs_algo
import Theorems.Thm_CircuitLowerBound_Alg_sat_Phi_of_pre
import Theorems.Thm_CircuitLowerBound_Oracle_ns_ans
import Theorems.Thm_CircuitLowerBound_Oracle_ns_io
import Theorems.Thm_CircuitLowerBound_Oracle_ns_sp
import Theorems.Thm_CircuitLowerBound_Oracle_one_self
import Theorems.Thm_CircuitLowerBound_Oracle_stk_inl
import Theorems.Thm_CircuitLowerBound_Oracle_stk_inr
import Theorems.Thm_CircuitLowerBound_Oracle_upd_ans
import Theorems.Thm_CircuitLowerBound_Oracle_upd_io
import Theorems.Thm_CircuitLowerBound_Oracle_upd_sp
import Theorems.Thm_CircuitLowerBound_Oracle_update_inl
import Theorems.Thm_CircuitLowerBound_Oracle_update_inr
import Theorems.Thm_CircuitLowerBound_Oracle_update_one
import Theorems.Thm_CircuitLowerBound_Parse_ones_unary_append
import Theorems.Thm_CircuitLowerBound_Time_exists_threshold
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_P2M_PaddedDescent_exists_tm__adb177e912aa
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] CircuitLowerBound.Oracle.ns_ans
attribute [local simp] CircuitLowerBound.Oracle.ns_io
attribute [local simp] CircuitLowerBound.Oracle.ns_sp
attribute [local simp] CircuitLowerBound.Oracle.one_self
attribute [local simp] CircuitLowerBound.Oracle.stk_inl
attribute [local simp] CircuitLowerBound.Oracle.stk_inr
attribute [local simp] CircuitLowerBound.Oracle.upd_ans
attribute [local simp] CircuitLowerBound.Oracle.upd_io
attribute [local simp] CircuitLowerBound.Oracle.upd_sp
attribute [local simp] CircuitLowerBound.Oracle.update_inl
attribute [local simp] CircuitLowerBound.Oracle.update_inr
attribute [local simp] CircuitLowerBound.Oracle.update_one
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
open ENP Groundwork Turing CircuitLowerBound
namespace Eight
theorem _root_.solution (hEng : StEngine) (h1 : StForm) (h2 : StNorm) (h3 : StCertSched) (h4 : StFlip) : StAlg := by
  intro c₀
  obtain ⟨a₀, g, F, hFp, hF⟩ := h1
  obtain ⟨fb, hbp, hb⟩ := h4
  have hF' : Alg.FormOK a₀ g F := hF
  have hb' : Alg.FlipOK fb := hb
  have hδ : (0 : ℝ) < 1 / (32 * ((3 * c₀ + a₀ + 1 : ℕ) : ℝ)) := by positivity
  obtain ⟨E, ⟨hEp⟩, cE, hE⟩ := hEng 3 (by norm_num) _ hδ
  have hE' : Alg.EngineOK E cE (1 / (32 * ((3 * c₀ + a₀ + 1 : ℕ) : ℝ))) := hE
  have := hEp
  have := Alg.isPolyT_algo (E := E) h3 hFp hbp
  obtain ⟨N, q, hfin, hN⟩ := PaddedDescent.exists_tm' (Alg.algo E F fb)
  refine ⟨N, hfin, ?_, fun e => ?_⟩
  · rintro m T ⟨y, ⟨ev⟩⟩
    obtain ⟨T', b, hr, hbi, -⟩ := Alg.runs_algo (fb := fb) hE' hF' (unary m ++ y)
    obtain ⟨ev'⟩ := hN _ _ _ _ hr
    have h5 := Alg.outputs_unique ev ev'
    have h6 : b = true := by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h5
      exact (N.outputAlphabet.symm.injective h5).symm
    have h7 := Alg.sat_Phi_of_pre hF' hb' _ (hbi.1 h6)
    rwa [Parse.ones_unary_append] at h7
  · obtain ⟨m₀, hm₀⟩ := Time.exists_threshold q cE c₀ a₀ (g e)
    refine ⟨max m₀ 1, fun m hm he hpos C hCl hC => ?_⟩
    obtain ⟨y, hy, hns, hNv⟩ := Alg.exists_guess hF' hb' h2 (le_of_max_le_right hm) hpos C hC
    obtain ⟨T, b, hr, hbi, hT⟩ := Alg.runs_algo (fb := fb) hE' hF' (unary m ++ y)
    obtain rfl : b = true := hbi.2 hns
    obtain ⟨ev⟩ := hN _ _ _ _ hr
    rw [he] at hNv
    have h8 := hm₀ m (le_of_max_le_left hm) C.length _ T hCl hNv hT
    have h9 : (unary m ++ y).length = m + 1 + ((m + C.length) + 1 + C.length * (4 + 2 * (m + C.length))) := by
      rw [List.length_append, hy]
      simp [unary]
    rw [← h9] at h8
    exact ⟨y, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans h8⟩⟩⟩
end Eight
