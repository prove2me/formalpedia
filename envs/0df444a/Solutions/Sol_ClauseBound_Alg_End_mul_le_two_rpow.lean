-- Prove2me | solution 1 for ClauseBound.Alg.End.mul_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:13:09.202761+00:00
-- url     : https://prove2.me/submissions/13631999-d8ab-4385-ae39-7237be08cbd3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_ClauseBound_Alg_End_one_le_log
import Theorems.Thm_ClauseBound_Alg_End_log_pow_le
import Theorems.Thm_ClauseBound_Alg_End_one_le_mul_of_div_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat
namespace ClauseBound.Alg.End
theorem _root_.solution {c k m : ℕ} {r : ℝ} (hc : 1 ≤ c) (hk : 1 ≤ k) (hm : 1 ≤ m) (h : 1 / ((c : ℝ) * Real.logb 2 ((m : ℝ) + 2) ^ c) ≤ r) :
    ((k * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * c * (3 * (c + 1).factorial * 2 ^ (c + 1)) : ℕ) : ℝ) * ((k : ℝ) * m * r)) := by
  have hy := one_le_log m
  have h1 := one_le_mul_of_div_le hc hy h
  have h2 := log_pow_le (c + 1) hm
  set y := Real.logb 2 ((m : ℝ) + 2) with hyd
  set D : ℕ := 3 * (c + 1).factorial * 2 ^ (c + 1)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hr : 0 ≤ r := le_trans (by positivity) h
  -- y ≤ c·D·m·r
  have h3 : y ≤ (c : ℝ) * D * (m * r) := by
    calc y = y * 1 := (mul_one y).symm
      _ ≤ y * ((c : ℝ) * y ^ c * r) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (c : ℝ) * r * y ^ (c + 1) := by ring
      _ ≤ (c : ℝ) * r * ((D : ℝ) * m) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (c : ℝ) * D * (m * r) := by ring
  have h4 : (k : ℝ) + y ≤ 2 * ((k : ℝ) * y) := by nlinarith
  have h5 : (k : ℝ) * y ≤ (c : ℝ) * D * ((k : ℝ) * m * r) := by
    calc (k : ℝ) * y ≤ (k : ℝ) * ((c : ℝ) * D * (m * r)) := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = _ := by ring
  have h6 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h7 : (m : ℝ) ≤ (2 : ℝ) ^ y := by
    rw [hyd, Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]; linarith
  calc ((k * m : ℕ) : ℝ) = (k : ℝ) * m := by push_cast; ring
    _ ≤ (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ y := mul_le_mul h6 h7 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((k : ℝ) + y) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
end ClauseBound.Alg.End
