-- Prove2me | solution 1 for Eliahou1993.rational_approx_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T14:39:53.362312+00:00
-- url     : https://prove2.me/submissions/aea037bd-f6f5-462e-9872-837ae4686a63

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/ContinuedFractions.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Section 4 / Theorem 1.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License

Copyright (c) 2026 Michal Wallace

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Theorems.Thm_Eliahou1993_farey_pair_bound
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 100000000
set_option maxRecDepth 10000

namespace Eliahou1993

theorem farey_13_15 : 301994 * 10781274 - 17087915 * 190537 = 1 := by
  norm_num

theorem conv14_lt_logb_three :
    (16785921 : ℝ) / 10590737 < Real.logb 2 3 := by
  rw [div_lt_iff₀'] <;> norm_num
  rw [Real.logb, mul_div, lt_div_iff₀]
  · rw [← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff] <;> norm_num
  · positivity

theorem logb_three_plus_lt_conv13 (m : ℕ) (hm : 2 ^ 40 < m) :
    Real.logb 2 (3 + 1 / (m : ℝ)) < (301994 : ℝ) / 190537 := by
  have h_log_bound : Real.logb 2 (3 + 1 / (m : ℝ)) < Real.logb 2 ((3 * 2 ^ 40 + 1) / 2 ^ 40) := by
    gcongr <;> norm_num
    nlinarith [show (m : ℝ) ≥ 2 ^ 40 + 1 by exact_mod_cast hm,
      inv_mul_cancel₀ (by positivity : (m : ℝ) ≠ 0)]
  refine lt_of_lt_of_le h_log_bound ?_
  rw [Real.logb_le_iff_le_rpow] <;> norm_num
  rw [Real.le_rpow_iff_log_le] <;> norm_num
  field_simp
  rw [mul_comm, ← Real.log_rpow, ← Real.log_rpow, Real.log_le_log_iff] <;> norm_num

end Eliahou1993

open Eliahou1993 in
theorem solution {k₁ L : ℕ} (hk₁ : 0 < k₁)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    17087915 ≤ L := by
  have h_bounds : (16785921 : ℚ) / 10590737 < (L : ℚ) / k₁ ∧ (L : ℚ) / k₁ < 301994 / 190537 := by
    apply And.intro;
    · convert conv14_lt_logb_three.trans hlower using 1;
      rw [ div_lt_div_iff₀ ] <;> norm_cast;
      rw [ div_lt_div_iff₀ ] <;> norm_cast;
    · have := logb_three_plus_lt_conv13 m hm;
      convert lt_of_le_of_lt hupper this using 1;
      norm_num [ div_lt_div_iff₀, hk₁ ];
      norm_cast;
  by_cases h_trichotomy : (L : ℚ) / k₁ > (17087915 : ℚ) / 10781274 ∨ (L : ℚ) / k₁ < (17087915 : ℚ) / 10781274 ∨ (L : ℚ) / k₁ = (17087915 : ℚ) / 10781274;
  · rcases h_trichotomy with h | h | h <;> norm_num at *;
    · have := farey_pair_bound (by norm_num : 0 < 10781274) (by norm_num : 0 < 190537) (by linarith : 0 < k₁) (farey_13_15) h h_bounds.right
      linarith;
    · rw [ div_lt_div_iff₀ ] at * <;> norm_cast at *;
      grind;
    · rw [ div_eq_div_iff ] at h <;> norm_cast at * <;> try linarith;
      grind;
  · grind
