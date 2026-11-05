-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.logb_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:25:43.97076+00:00
-- url     : https://prove2.me/submissions/d9611050-39c2-4e30-9c09-61e03b45d882

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F
namespace ClauseBound.Alg.TopArith
theorem _root_.solution (K n : ℕ) (hK : 2 ≤ K) : Real.logb 2 K ^ n ≤ (n.factorial * 2 ^ n : ℕ) * (K : ℝ) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hK0 : (0 : ℝ) < K := by linarith
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  have h1 := Real.pow_div_factorial_le_exp (Real.log K) hlog n
  rw [Real.exp_log hK0] at h1
  have h2 : Real.log K ^ n ≤ n.factorial * K := by
    rwa [div_le_iff₀' (by positivity)] at h1
  have h3 : Real.logb 2 K ≤ 2 * Real.log K := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h2 : (1 : ℝ) - 2⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    have h2' : (1 : ℝ) / 2 ≤ Real.log 2 := by norm_num at h2 ⊢; linarith
    nlinarith
  have h4 : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) hK1
  calc Real.logb 2 K ^ n ≤ (2 * Real.log K) ^ n := pow_le_pow_left₀ h4 h3 n
    _ = 2 ^ n * Real.log K ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (n.factorial * K) := by gcongr
    _ = (n.factorial * 2 ^ n : ℕ) * (K : ℝ) := by push_cast; ring
end ClauseBound.Alg.TopArith
