-- Prove2me | solution 1 for Eliahou1993.eliahou_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T14:41:05.177286+00:00
-- url     : https://prove2.me/submissions/519d59f9-0b63-4953-8b6e-a899ae8b7058

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/Sandwich.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Theorem 2.1.
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
import Definitions.Def_eliahou1993Cycle
import Theorems.Thm_Eliahou1993_eliahou_product_formula_real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset BigOperators Real

set_option maxHeartbeats 800000

namespace Eliahou1993

theorem prod_le_pow_min {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) ≤
    (3 + 1 / (c.minElem : ℝ)) ^ c.numOdd := by
  have h := Finset.prod_le_prod (s := c.oddIndices)
    (f := fun i => (3 + 1 / (c.seq i : ℝ))) (g := fun _ => (3 + 1 / (c.minElem : ℝ)))
    (fun i _ => by positivity) (fun i _ => by
      gcongr
      · exact_mod_cast CollatzCycle.minElem_pos c
      · exact CollatzCycle.minElem_le c i)
  rw [Finset.prod_const] at h
  exact h

theorem pow_max_le_prod {L : ℕ} (c : CollatzCycle L) :
    (3 + 1 / (c.maxElem : ℝ)) ^ c.numOdd ≤
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) := by
  have h_prod_ge : ∀ i ∈ c.oddIndices, (3 + 1 / (c.maxElem : ℝ)) ≤ 3 + 1 / (c.seq i : ℝ) := by
    intros i hi; gcongr;
    · exact_mod_cast c.pos i;
    · exact c.le_maxElem i;
  have h := Finset.prod_le_prod (s := c.oddIndices)
    (f := fun _ => (3 + 1 / (c.maxElem : ℝ))) (g := fun i => 3 + 1 / (c.seq i : ℝ))
    (fun _ _ => by positivity) h_prod_ge
  rw [Finset.prod_const] at h
  exact h

theorem two_pow_le_bound_min {L : ℕ} (c : CollatzCycle L) :
    (2 : ℝ) ^ L ≤ (3 + 1 / (c.minElem : ℝ)) ^ c.numOdd := by
  rw [← eliahou_product_formula_real c]
  exact prod_le_pow_min c

theorem bound_max_le_two_pow {L : ℕ} (c : CollatzCycle L) :
    (3 + 1 / (c.maxElem : ℝ)) ^ c.numOdd ≤ (2 : ℝ) ^ L := by
  rw [← eliahou_product_formula_real c]
  exact pow_max_le_prod c

theorem ratio_le_log {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ)) := by
  have hk' : (0 : ℝ) < c.numOdd := by exact_mod_cast hk
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.log_le_log (by positivity) (two_pow_le_bound_min c)
  rw [Real.log_pow, Real.log_pow] at h
  rw [div_le_iff₀ hk', Real.logb, div_mul_eq_mul_div, le_div_iff₀ hlog2]
  linarith

theorem log_le_ratio {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd := by
  rw [ le_div_iff₀ ( by positivity ), mul_comm ];
  rw [ ← Real.logb_pow, Real.logb_le_iff_le_rpow ] <;> norm_cast;
  · convert bound_max_le_two_pow c using 1;
    norm_cast;
  · positivity

end Eliahou1993

open Eliahou1993 in
theorem solution {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd ∧
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ)) :=
  ⟨log_le_ratio c hk, ratio_le_log c hk⟩
