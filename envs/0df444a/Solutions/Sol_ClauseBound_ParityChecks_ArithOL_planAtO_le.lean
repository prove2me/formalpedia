-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.planAtO_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:37:13.185519+00:00
-- url     : https://prove2.me/submissions/66583d2a-6a00-43da-864c-434f97302c11

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
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_two_le_D
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_needO_le
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_planAtO_getD_le
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_D_le_log
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_le_of_W
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_le_of_lt_n0
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_combineO
import Theorems.Thm_ClauseBound_ParityChecks_LD_two_pow
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_Wof_ge
import Theorems.Thm_ClauseBound_TopN_Arith_le_of_small
import Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (i : Idx) {e : ℝ} {C C₀ k n n₀ s A₁ : ℕ} (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e) (heK : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C)
    (hM : ((Wof k (S.K i) s : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (((planAtO S (cO k C C₀) n₀ k n i s).getD n : ℕ) : ℝ) ≤
      (((354 * k * ckN k + ccO k C₀ * A₁ + 1 : ℕ) : ℝ) + ((2 ^ s0K k : ℕ) : ℝ) + (A₁ : ℝ) + ((n₀ ^ C₀ : ℕ) : ℝ)) * n * e * ((s : ℝ) + 1) := by
  obtain ⟨p1, p2⟩ := planAtO_getD_le hS (cO k C C₀) n₀ k n i s
  have pn : (((planAtO S (cO k C C₀) n₀ k n i s).getD n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast p1
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) hs
  have hq : (1 : ℝ) ≤ (s : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  obtain ⟨w1, -, -, -, -, -, w7, -⟩ := Wof_ge (k := k) (s := s) hK1
  refine combineO (Nat.cast_nonneg n) he0.le hq (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_
  by_cases c1 : s0K k ≤ s
  · by_cases c2 : 2 ^ betaN k s ≤ n + 1
    · by_cases c3 : n₀ ≤ n
      · by_cases c5 : 2 * LD (2 ^ betaN k s) ≤ n
        · have h3 : (((planAtO S (cO k C C₀) n₀ k n i s).getD n : ℕ) : ℝ) ≤ (needO S k i n s : ℝ) := by
            exact_mod_cast p2 ⟨c1, c2, c3, D_le_log hK hKn heK h2, c5⟩
          exact Or.inl (h3.trans (needO_le S i hK hn17 hlt c2 he0 he1 hs hM hrate))
        · rw [LD_two_pow] at c5
          have hD2 := two_le_D k s
          have h4 : 2 * (betaN k s + 1) ≤ (betaN k s + 3) * 2 ^ betaN k s := by
            calc 2 * (betaN k s + 1) = (betaN k s + 1) * 2 := by ring
              _ ≤ (betaN k s + 3) * 2 ^ betaN k s := Nat.mul_le_mul (by omega) hD2
          exact Or.inr (Or.inr (Or.inl (pn.trans (le_of_W hKn he0.le (by omega) hM))))
      · exact Or.inr (Or.inr (Or.inr (pn.trans (le_of_lt_n0 hK hKn (not_le.1 c3) heK))))
    · exact Or.inr (Or.inr (Or.inl (pn.trans (le_of_W hKn he0.le (by omega) hM))))
  · exact Or.inr (Or.inl (pn.trans (le_of_small (not_le.1 c1).le hs)))
end ClauseBound.ParityChecks.ArithOL
