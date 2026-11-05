-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.D_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:32.688069+00:00
-- url     : https://prove2.me/submissions/f7bb979d-9cb3-4f7f-b706-1fbe69d574bd

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
import Theorems.Thm_ClauseBound_Alg_TopArith_logb_le_of_le_pow
import Theorems.Thm_ClauseBound_TopN_Arith_D_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution {K n s C C₀ k : ℕ} {e : ℝ} (hK : 2 ≤ K) (hKn : K ≤ n) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C) :
    2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ cO k C C₀ := by
  have hD := D_le (k := k) hK he h2
  have hy : Real.logb 2 K ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) :=
    logb_le_of_le_pow K (Nat.log 2 n + 1) (by omega) (hKn.trans (Nat.lt_pow_succ_log_self (by norm_num) n).le)
  have hy0 : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ K))
  have hL : 2 ≤ Nat.log 2 n + 1 := by
    have := Nat.log_pos (b := 2) (by norm_num) (hK.trans hKn)
    omega
  have ha : a0 k C ≤ (Nat.log 2 n + 1) ^ Nat.size (a0 k C) := (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_left hL _)
  have har : (a0 k C : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ Nat.size (a0 k C) := by exact_mod_cast ha
  have hfin : ((2 ^ betaN k s : ℕ) : ℝ) ≤ (((Nat.log 2 n + 1) ^ cO k C C₀ : ℕ) : ℝ) := by
    calc ((2 ^ betaN k s : ℕ) : ℝ) ≤ (a0 k C : ℝ) * Real.logb 2 K ^ (4 * cK k * C * C₀) := hD
      _ ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ Nat.size (a0 k C) * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (4 * cK k * C * C₀) :=
          mul_le_mul har (pow_le_pow_left₀ hy0 hy _) (pow_nonneg hy0 _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (((Nat.log 2 n + 1) ^ cO k C C₀ : ℕ) : ℝ) := by rw [← pow_add, cO]; push_cast; rfl
  exact_mod_cast hfin
end ClauseBound.ParityChecks.ArithOL
