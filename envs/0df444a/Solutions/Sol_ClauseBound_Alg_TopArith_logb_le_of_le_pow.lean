-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.logb_le_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:32.819047+00:00
-- url     : https://prove2.me/submissions/1773bf94-8359-47c1-9332-0b6c627e28ff

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
theorem _root_.solution (x n : ℕ) (hx : 1 ≤ x) (h : x ≤ 2 ^ n) : Real.logb 2 x ≤ n := by
  have h' : (x : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast h
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  calc Real.logb 2 x ≤ Real.logb 2 ((2 : ℝ) ^ n) := Real.logb_le_logb_of_le (by norm_num) hx' h'
    _ = n := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
end ClauseBound.Alg.TopArith
