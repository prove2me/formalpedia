-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.needO_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:20:36.855864+00:00
-- url     : https://prove2.me/submissions/fae01a88-2bf3-4a27-810b-caef409d4706

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
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_UbO_le
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_argO_le
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_lowerOR
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_real_coreM
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_real_finalO
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_needO_le_sum
import Theorems.Thm_ClauseBound_Alg_TopArith_logb_le_of_le_pow
import Theorems.Thm_ClauseBound_Alg_TopArith_two_g_div
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_ParityChecks_one_le_PbOL
import Theorems.Thm_ClauseBound_TopN_Arith_b_le_lin
import Theorems.Thm_ClauseBound_TopN_Arith_lamS_mul_le
import Theorems.Thm_ClauseBound_TopN_Arith_one_le_lamS
import Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_two_g_div
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
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n s A₁ : ℕ} (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (hD : 2 ^ betaN k s ≤ n + 1) (he0 : 0 < e) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e)
    (hM : ((Wof k (S.K i) s : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needO S k i n s : ℝ) ≤ ((354 * k * ckN k + ccO k C₀ * A₁ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1) := by
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn1 : 1 ≤ n := hK1.trans hKn
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := lowerOR (k := k) (s := s) (C₀ := C₀) hK hn17 hlt
  have harg := argO_le (k := k) (s := s) (C₀ := C₀) hK hn17 hlt hD
  have hlam1 := one_le_lamS hK1 (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))
  have hlamK := lamS_mul_le (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))
  have hUb := UbO_le (k := k) (K := S.K i) (s := s) hn1
  have hB1 : 1 ≤ bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 := by
    have e1 : bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 = PbOL (S.K i) n (2 ^ betaN k s) * (6 * S.K i ^ 7) := by
      simp [bitsS, Arith.two_g_div hK1]
    rw [e1]
    exact Nat.mul_pos (one_le_PbOL hn1 hK1) (by positivity)
  have hr := hrate _ _ hlam1 hB1
  have hsum := needO_le_sum S i hD
  have hlog : Real.logb 2 ((S.K i : ℝ) * ((lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s)) : ℝ) +
      (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 : ℝ))) ≤ ((5 * (17 * C₀ * (S.K i).size) + 16 : ℕ) : ℝ) := by
    have h := logb_le_of_le_pow _ _ (Nat.mul_pos hK1 (Nat.add_pos_left hlam1 _)) harg
    push_cast at h ⊢
    exact h
  generalize S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))) (),
    List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0) ()) = nd at hr hsum
  generalize bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 = Bt at hr hlog
  generalize lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s)) = lam at hr hlog hsum r3 hlamK
  have rU : ((UbOL k (S.K i) n (2 ^ betaN k s) : ℕ) : ℝ) ≤ 354 * (k : ℝ) * n * ((betaN k s + 1 : ℕ) : ℝ) + ((54 * S.K i ^ 16 : ℕ) : ℝ) := by exact_mod_cast hUb
  have rL : (lam : ℝ) * (S.K i : ℝ) ^ 3 ≤ (S.K i : ℝ) ^ 3 + (S.K i : ℝ) * ((UbOL k (S.K i) n (2 ^ betaN k s) : ℕ) : ℝ) +
      ((3 * S.K i ^ 8 * PbOL (S.K i) n (2 ^ betaN k s) : ℕ) : ℝ) := by
    exact_mod_cast hlamK
  have rS : (needO S k i n s : ℝ) ≤ (((3 * S.K i ^ 8 * (S.K i).size : ℕ) : ℝ) + ((PbOL (S.K i) n (2 ^ betaN k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) : ℕ) : ℝ) +
      (((S.K i - 1) * lam : ℕ) : ℝ) + (nd : ℝ) + ((3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) : ℕ) : ℝ) +
      (((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ)) + ((n / 2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have rb : ((betaN k s + 1 : ℕ) : ℝ) ≤ (ckN k : ℝ) * ((s : ℝ) + 1) := by
    have : betaN k s + 1 ≤ ckN k * (s + 1) := (by omega : betaN k s + 1 ≤ betaN k s + 3).trans (b_le_lin k s)
    exact_mod_cast this
  have rdiv : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) * e := by
    have h1 : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ s : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : (n : ℝ) / ((2 ^ s : ℕ) : ℝ) = (n : ℝ) * (1 / (2 : ℝ) ^ s) := by push_cast; ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n))
  have hKr : (0 : ℝ) < (S.K i : ℝ) := by exact_mod_cast hK1
  have core := real_coreM (A := (A₁ : ℝ)) hKr he0 he1 (Nat.cast_nonneg n) (Nat.cast_nonneg C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hM r1 r2 r3 r4 r5 r6 r7 r8 r9 rU rL hr hlog
  have ecc : (3 + ((3 * GO C₀ : ℕ) : ℝ) + ((55 + 354 * k + GO C₀ : ℕ) : ℝ) + (GO C₀ : ℝ) + 54 + 1 + ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) + ((27 * (4 + 17 * C₀) : ℕ) : ℝ) +
      ((17 + 51 * C₀ : ℕ) : ℝ)) * (A₁ : ℝ) = ((ccO k C₀ * A₁ : ℕ) : ℝ) := by
    unfold ccO; push_cast; ring
  rw [ecc] at core
  have hq : (1 : ℝ) ≤ (s : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  have fin := real_finalO (ck := (ckN k : ℝ)) (q := (s : ℝ) + 1) he0.le (Nat.cast_nonneg n) (Nat.cast_nonneg k) hq (Nat.cast_nonneg _) rb core rdiv rS
  have efin : ((354 * k * ckN k + ccO k C₀ * A₁ + 1 : ℕ) : ℝ) = 354 * (k : ℝ) * (ckN k : ℝ) + ((ccO k C₀ * A₁ : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [efin]
  exact fin
end ClauseBound.ParityChecks.ArithOL
