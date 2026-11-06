-- Prove2me | solution 1 for CircuitLowerBound.Time.final_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:43.819525+00:00
-- url     : https://prove2.me/submissions/ccf66693-bd55-4ed3-8312-733d567e2e2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Time

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
open CircuitLowerBound.Time
namespace CircuitLowerBound.Time
theorem _root_.solution (K : ℕ) {m : ℕ} (hm : 16 * (K + 1) ≤ m) :
    (K : ℝ) * ((2 : ℝ) ^ ((1 / 32 : ℝ) * m) * (2 : ℝ) ^ ((1 / 32 : ℝ) * m)) ≤ (2 : ℝ) ^ (((m / 8 : ℕ) : ℝ)) := by
  have h1 : m < 8 * (m / 8 + 1) := Nat.lt_mul_div_succ m (by norm_num)
  have h2 : (m : ℝ) ≤ 8 * (((m / 8 : ℕ) : ℝ) + 1) := by exact_mod_cast h1.le
  have h3 : (16 : ℝ) * ((K : ℝ) + 1) ≤ m := by exact_mod_cast hm
  have h4 : (1 / 32 : ℝ) * m + (1 / 32 : ℝ) * m + K ≤ ((m / 8 : ℕ) : ℝ) := by linarith
  have h5 : (K : ℝ) ≤ (2 : ℝ) ^ (K : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self (n := K)).le
  calc (K : ℝ) * ((2 : ℝ) ^ ((1 / 32 : ℝ) * m) * (2 : ℝ) ^ ((1 / 32 : ℝ) * m))
      ≤ (2 : ℝ) ^ (K : ℝ) * ((2 : ℝ) ^ ((1 / 32 : ℝ) * m) * (2 : ℝ) ^ ((1 / 32 : ℝ) * m)) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = (2 : ℝ) ^ ((1 / 32 : ℝ) * m + (1 / 32 : ℝ) * m + K) := by
        rw [Real.rpow_add two_pos, Real.rpow_add two_pos]
        ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two h4
end CircuitLowerBound.Time
