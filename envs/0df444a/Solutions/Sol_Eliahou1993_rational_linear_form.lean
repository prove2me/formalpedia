-- Prove2me | solution 1 for Eliahou1993.rational_linear_form
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T14:39:54.022124+00:00
-- url     : https://prove2.me/submissions/79e098fe-6842-49bb-9677-a6ff12ead14e

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, files Collatz/ContinuedFractions.lean
and Collatz/LinearForm.lean), formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Theorem 1.1.
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
import Theorems.Thm_Eliahou1993_farey_intermediate_coeffs
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

set_option maxHeartbeats 8000000
set_option exponentiation.threshold 100000000
set_option maxRecDepth 10000

namespace Eliahou1993

theorem farey_13_15 : 301994 * 10781274 - 17087915 * 190537 = 1 := by
  norm_num

theorem coprime_15 : Nat.Coprime 17087915 10781274 := by
  norm_num

theorem farey_15_16 : 17087915 * 53715833 - 85137581 * 10781274 = 1 := by
  norm_num

theorem conv16_lt_logb_three :
    (85137581 : ℝ) / 53715833 < Real.logb 2 3 := by
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

private theorem rat_of_real_div_lt {a b c d : ℕ}
    (_hb : 0 < b) (_hd : 0 < d)
    (h : (a : ℝ) / b < (c : ℝ) / d) :
    (a : ℚ) / b < (c : ℚ) / d := by
  have : ((a : ℚ) / b : ℝ) < ((c : ℚ) / d : ℝ) := by
    simpa using h
  exact_mod_cast this

end Eliahou1993

open Eliahou1993 in
theorem solution {k₁ L : ℕ} (hk₁ : 0 < k₁)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    ∃ (a b c : ℕ), 0 < b ∧ a * c = 0 ∧
      L = 301994 * a + 17087915 * b + 85137581 * c := by
  have h_low : (85137581 : ℚ) / 53715833 < (L : ℚ) / k₁ :=
    rat_of_real_div_lt (by norm_num) hk₁ (conv16_lt_logb_three.trans hlower)
  have h_high : (L : ℚ) / k₁ < (301994 : ℚ) / 190537 :=
    rat_of_real_div_lt hk₁ (by norm_num)
      (lt_of_le_of_lt hupper (logb_three_plus_lt_conv13 m hm))
  rcases lt_trichotomy ((L : ℚ) / k₁) ((17087915 : ℚ) / 10781274) with hlt | heq | hgt
  · obtain ⟨cCoeff, bCoeff, hc, hb, hL, _⟩ :=
      farey_intermediate_coeffs
        (by norm_num : 0 < 53715833) (by norm_num : 0 < 10781274) hk₁
        farey_15_16 h_low hlt
    refine ⟨0, bCoeff, cCoeff, hb, by simp, ?_⟩
    linarith [hL]
  · have heqN : L * 10781274 = 17087915 * k₁ := by
      have h := (div_eq_div_iff (by exact_mod_cast hk₁.ne' : (k₁ : ℚ) ≠ 0)
        (by norm_num : (10781274 : ℚ) ≠ 0)).mp heq
      exact_mod_cast h
    have hdiv : 17087915 ∣ L := by
      have : 17087915 ∣ 10781274 * L := ⟨k₁, by linarith [heqN]⟩
      exact coprime_15.dvd_of_dvd_mul_left this
    obtain ⟨b, rfl⟩ := hdiv
    have hbpos : 0 < b := by
      have hlogpos : (0 : ℝ) < Real.logb 2 3 :=
        Real.logb_pos (by norm_num) (by norm_num)
      have hpos : 0 < ((17087915 * b : ℕ) : ℝ) / k₁ := lt_trans hlogpos hlower
      exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
    exact ⟨0, b, 0, hbpos, by simp, by ring⟩
  · obtain ⟨aF, bF, haF, hbF, hL, _⟩ :=
      farey_intermediate_coeffs
        (by norm_num : 0 < 10781274) (by norm_num : 0 < 190537) hk₁
        farey_13_15 hgt h_high
    refine ⟨bF, aF, 0, haF, by simp, ?_⟩
    linarith [hL]
