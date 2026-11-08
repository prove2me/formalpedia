-- Prove2me | solution 1 for Eliahou1993.eliahou_product_formula_real
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T14:39:52.742097+00:00
-- url     : https://prove2.me/submissions/d8768459-c956-435c-8482-3694b2898ed7

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/ProductFormula.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Lemma 2.2.
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
import Theorems.Thm_Eliahou1993_eliahou_product_formula
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators

set_option maxHeartbeats 800000

open Eliahou1993 in
theorem solution {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) = (2 : ℝ) ^ L := by
  convert congr_arg ( fun x : ℕ => x / ∏ i ∈ c.oddIndices, ( c.seq i : ℝ ) ) ( show ( ∏ i ∈ c.oddIndices, ( 3 * c.seq i + 1 ) : ℕ ) = 2 ^ L * ∏ i ∈ c.oddIndices, ( c.seq i : ℕ ) from ?_ ) using 1;
  · norm_num [ add_div' ];
    rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ] ; intros ; rw [ inv_eq_one_div, add_div, mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| c.pos _ ) ];
  · rw [ eq_div_iff ] <;> norm_cast ; simp +decide [ Finset.prod_eq_zero_iff, ne_of_gt ( c.pos _ ) ];
  · exact eliahou_product_formula c
