-- Prove2me | solution 1 for ClauseBound.TopN.End.log_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:28:04.603623+00:00
-- url     : https://prove2.me/submissions/e48c7443-caf9-4665-a682-5952b795f61d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_TopN_End
import Theorems.Thm_ClauseBound_Alg_End_log_pow_le
import Theorems.Thm_ClauseBound_Alg_End_one_le_log
import Theorems.Thm_ClauseBound_Alg_End_one_le_mul_of_div_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End
namespace ClauseBound.TopN.End
theorem _root_.solution {c n : ℕ} {r : ℝ} (hc : 1 ≤ c) (hn : 1 ≤ n) (h : 1 / ((c : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ c) ≤ r) :
    Real.logb 2 ((n : ℝ) + 2) ≤ ((c * (3 * (c + 1).factorial * 2 ^ (c + 1)) : ℕ) : ℝ) * ((n : ℝ) * r) := by
  have hy := one_le_log n
  have h1 := one_le_mul_of_div_le hc hy h
  have h2 := log_pow_le (c + 1) hn
  set y := Real.logb 2 ((n : ℝ) + 2) with hyd
  set D : ℕ := 3 * (c + 1).factorial * 2 ^ (c + 1)
  have hr : 0 ≤ r := le_trans (by positivity) h
  calc y = y * 1 := (mul_one y).symm
    _ ≤ y * ((c : ℝ) * y ^ c * r) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (c : ℝ) * r * y ^ (c + 1) := by ring
    _ ≤ (c : ℝ) * r * ((D : ℝ) * n) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((c * D : ℕ) : ℝ) * ((n : ℝ) * r) := by push_cast; ring
end ClauseBound.TopN.End
