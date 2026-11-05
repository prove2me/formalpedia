-- Prove2me | solution 1 for ClauseBound.TopN.Arith.le_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:43:52.011617+00:00
-- url     : https://prove2.me/submissions/64fd58bb-a730-4eb3-8e49-1a2fc7321a84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_ArithR
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
namespace ClauseBound.TopN.Arith
theorem _root_.solution {s t n : ℕ} {e : ℝ} (hst : s ≤ t) (g1 : 1 / (2 : ℝ) ^ s ≤ e) : (n : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) * ((n : ℝ) * e) := by
  have a1 : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hst
  have a2 : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have a3 : 1 ≤ e * (2 : ℝ) ^ s := by rwa [div_le_iff₀ a2] at g1
  have he0 : 0 ≤ e := le_trans (by positivity) g1
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ t * e := by
    have := mul_le_mul_of_nonneg_left a1 he0
    linarith
  push_cast
  calc (n : ℝ) = n * 1 := (mul_one _).symm
    _ ≤ n * ((2 : ℝ) ^ t * e) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
    _ = (2 : ℝ) ^ t * ((n : ℝ) * e) := by ring
end ClauseBound.TopN.Arith
