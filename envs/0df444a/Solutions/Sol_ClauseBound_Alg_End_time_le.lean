-- Prove2me | solution 1 for ClauseBound.Alg.End.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:48:39.295933+00:00
-- url     : https://prove2.me/submissions/6a7d2653-0eb4-46c0-8bbe-f559c9ddd7c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat
namespace ClauseBound.Alg.End
theorem _root_.solution (q L E T H G : ℕ) {X : ℝ} (hX : 0 ≤ X) (hT1 : 1 ≤ T) (hL : L + 1 ≤ 8 * T ^ 2) (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((H : ℝ) * X))
    (hE : (E : ℝ) ≤ (G : ℝ) * X) :
    ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤ ((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * (2 : ℝ) ^ (((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * X) := by
  have h1 : L + 2 ^ E + 1 ≤ 9 * (T ^ 2 * 2 ^ E) := by
    have a : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    have b : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ hT1
    nlinarith
  have h2 : ((T ^ 2 * 2 ^ E : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X) := by
    have e1 : ((2 : ℝ) ^ ((H : ℝ) * X)) ^ 2 = (2 : ℝ) ^ (2 * (H : ℝ) * X) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
    have e2 : ((2 : ℝ) ^ E) ≤ (2 : ℝ) ^ ((G : ℝ) * X) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
    calc ((T ^ 2 * 2 ^ E : ℕ) : ℝ) = (T : ℝ) ^ 2 * (2 : ℝ) ^ E := by push_cast; ring
      _ ≤ ((2 : ℝ) ^ ((H : ℝ) * X)) ^ 2 * (2 : ℝ) ^ ((G : ℝ) * X) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hT 2) e2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X) := by
          rw [e1, ← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
  have h3 : ((L + 2 ^ E + 1 : ℕ) : ℝ) ≤ 9 * (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X) := by
    calc ((L + 2 ^ E + 1 : ℕ) : ℝ) ≤ ((9 * (T ^ 2 * 2 ^ E) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = 9 * ((T ^ 2 * 2 ^ E : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : ((2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X)) ^ q = (2 : ℝ) ^ (((q * (2 * H + G) : ℕ) : ℝ) * X) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  have h5 : (2 : ℝ) ^ (((q * (2 * H + G) : ℕ) : ℝ) * X) ≤ (2 : ℝ) ^ (((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * X) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right ?_ hX)
    exact_mod_cast Nat.le_add_left _ _
  have h6 : ((q * 9 ^ q : ℕ) : ℝ) ≤ ((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
  calc ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) = (q : ℝ) * ((L + 2 ^ E + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (9 * (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X)) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 q) (by positivity)
    _ = ((q * 9 ^ q : ℕ) : ℝ) * (2 : ℝ) ^ (((q * (2 * H + G) : ℕ) : ℝ) * X) := by rw [mul_pow, h4]; push_cast; ring
    _ ≤ _ := mul_le_mul h6 h5 (by positivity) (by positivity)
end ClauseBound.Alg.End
