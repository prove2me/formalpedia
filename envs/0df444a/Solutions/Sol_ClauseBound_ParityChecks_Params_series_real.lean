-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.series_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:39:03.168677+00:00
-- url     : https://prove2.me/submissions/6811d575-f5fd-4d0e-bd92-46757f7ee7ca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_term_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution {u nb i₀ m h : ℕ} (hu : u ≤ m) (hi0 : 1 ≤ i₀) (hnb : 1 ≤ nb) (hh : 1 ≤ h) (key : 6 * m * 2 ^ h ≤ nb * i₀) :
    |(1 - 2 * (1 / (nb : ℝ))) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * (1 / (nb : ℝ))) ^ i * (u.choose i : ℝ)| ≤ 2 * (1 / 2 ^ h) ^ i₀ := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = -2 * (1 / (nb : ℝ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 / 2 ^ h := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq2 : q ≤ 1 / 2 := by
    rw [hq]
    apply one_div_le_one_div_of_le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) hh
  have e1 : (1 - 2 * (1 / (nb : ℝ))) ^ u = ∑ i ∈ range (u + 1), y ^ i * (u.choose i : ℝ) := by
    rw [show 1 - 2 * (1 / (nb : ℝ)) = y + 1 by rw [hy]; ring, add_pow]
    refine sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one]
  have e2 : ∑ i ∈ range (u + 1), y ^ i * (u.choose i : ℝ) = ∑ i ∈ range (i₀ + 1 + u), y ^ i * (u.choose i : ℝ) := by
    refine sum_subset (range_mono (by omega)) fun i _ hi => ?_
    rw [Nat.choose_eq_zero_of_lt (by have := mem_range.not.1 hi; omega)]
    simp
  rw [e1, e2, sum_range_add, ← hy, add_sub_cancel_left, ← hq]
  calc |∑ j ∈ range u, y ^ (i₀ + 1 + j) * (u.choose (i₀ + 1 + j) : ℝ)|
      ≤ ∑ j ∈ range u, |y ^ (i₀ + 1 + j) * (u.choose (i₀ + 1 + j) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range u, q ^ (i₀ + 1 + j) := by
        refine sum_le_sum fun j _ => ?_
        rw [hy, hq]
        exact term_le hu (by omega) hi0 hnb key
    _ = q ^ (i₀ + 1) * ∑ j ∈ range u, q ^ j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => pow_add _ _ _
    _ ≤ q ^ (i₀ + 1) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_trans (sum_le_sum fun j _ => pow_le_pow_left₀ hq0 hq2 j) (sum_geometric_two_le u)
    _ ≤ 2 * q ^ i₀ := by
        rw [pow_succ]
        have h1 : 0 ≤ q ^ i₀ := by positivity
        nlinarith
end ClauseBound.ParityChecks.Params
