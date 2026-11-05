-- Prove2me | solution 1 for ClauseBound.Alg.End.log_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:25:14.820723+00:00
-- url     : https://prove2.me/submissions/498084a1-1ac5-41ce-8760-3b3c44ae88ef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_ClauseBound_Alg_End_one_le_log

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat
namespace ClauseBound.Alg.End
theorem _root_.solution (j : ℕ) {m : ℕ} (hm : 1 ≤ m) : Real.logb 2 ((m : ℝ) + 2) ^ j ≤ ((3 * j.factorial * 2 ^ j : ℕ) : ℝ) * m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hx : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  have h1 := Real.pow_div_factorial_le_exp _ hx j
  rw [Real.exp_log hpos] at h1
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  rw [div_le_iff₀ hf] at h1
  have l2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2 : Real.logb 2 ((m : ℝ) + 2) ≤ 2 * Real.log ((m : ℝ) + 2) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h0 : 0 ≤ Real.logb 2 ((m : ℝ) + 2) := by linarith [one_le_log m]
  calc Real.logb 2 ((m : ℝ) + 2) ^ j ≤ (2 * Real.log ((m : ℝ) + 2)) ^ j := pow_le_pow_left₀ h0 h2 j
    _ = 2 ^ j * Real.log ((m : ℝ) + 2) ^ j := mul_pow _ _ _
    _ ≤ 2 ^ j * (((m : ℝ) + 2) * j.factorial) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 2 ^ j * ((3 * (m : ℝ)) * j.factorial) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hf.le) (by positivity)
    _ = ((3 * j.factorial * 2 ^ j : ℕ) : ℝ) * m := by push_cast; ring
end ClauseBound.Alg.End
