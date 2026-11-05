-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.le_logb_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:36:22.661697+00:00
-- url     : https://prove2.me/submissions/8ce5b031-9ca1-4758-b426-547182ec94ef

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
theorem _root_.solution (x n : ℕ) (h : 2 ^ n ≤ x) : (n : ℝ) ≤ Real.logb 2 x := by
  have h' : (2 : ℝ) ^ n ≤ (x : ℝ) := by exact_mod_cast h
  calc (n : ℝ) = Real.logb 2 ((2 : ℝ) ^ n) := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ ≤ Real.logb 2 x := Real.logb_le_logb_of_le (by norm_num) (by positivity) h'
end ClauseBound.Alg.TopArith
