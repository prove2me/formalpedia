-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.planAtO_getD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:46.683207+00:00
-- url     : https://prove2.me/submissions/56ee116b-f690-4020-aaf6-3e161406355a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
attribute [local fun_prop] Groundwork.PolyT.all
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
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (c n₀ k n : ℕ) (i : Idx) (s : ℕ) :
    (planAtO S c n₀ k n i s).getD n ≤ n ∧
      ((s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n) →
        (planAtO S c n₀ k n i s).getD n ≤ needO S k i n s) := by
  unfold planAtO needNetC needO needNet
  set x : Idx × U × U := (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s))) (),
    List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (blockN k n s)) 0) ()) with hx
  set a := max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PbOL (S.K i) n (blockN k n s) * (2 * (3 * S.K i ^ 8) / S.K i + 1))
  set d := (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s))
  set r := restO k (S.K i) n s
  by_cases hc : s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n
  · rw [if_pos hc]
    cases h : S.needC (List.replicate n (), x) with
    | none =>
      refine ⟨by simp, fun _ => ?_⟩
      simp only [Option.map_none, Option.bind_none, Option.getD_none]
      by_contra hlt
      have h1 : S.need x ≤ (List.replicate n ()).length := by
        have : S.need x ≤ max a (max d (S.need x)) := (le_max_right _ _).trans (le_max_right _ _)
        simp only [List.length_replicate]
        omega
      rw [hS.needC_some _ x h1] at h
      cases h
    | some v =>
      have hv := hS.needC_eq _ x v h
      subst hv
      simp only [Option.map_some, Option.bind_some]
      split_ifs with h1
      · exact ⟨by simpa using h1, fun _ => by simp⟩
      · exact ⟨by simp, fun _ => by simpa using (not_le.1 h1).le⟩
  · rw [if_neg hc]
    exact ⟨by simp, fun h1 => absurd h1 hc⟩
end ClauseBound.ParityChecks.ArithOL
