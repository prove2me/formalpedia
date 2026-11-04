-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_discount_stieltjes_clock_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:31:55.72557+00:00
-- url     : https://prove2.me/submissions/14b22c9d-65b7-4558-827a-fd9e37dc7c27

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal BigOperators
open AvramDividend.Classical

/-- Every discounted clock correction is nonpositive along an increasing
finite grid when the candidate values are nonnegative. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hmono : ∀ i, i < n → u i ≤ u (i + 1))
    (b : ℝ≥0) (hfinal : u n ≤ b)
    (f : ℕ → ℝ) (fb : ℝ)
    (hf : ∀ i, i < n → 0 ≤ f (i + 1)) (hfb : 0 ≤ fb) :
    (∑ i ∈ Finset.range n,
        (Real.exp (-(q * (u (i + 1) : ℝ))) -
          Real.exp (-(q * (u i : ℝ)))) * f (i + 1)) +
      (Real.exp (-(q * (b : ℝ))) -
        Real.exp (-(q * (u n : ℝ)))) * fb ≤ 0 := by
  have hneg (i : ℕ) (hi : i < n) :
      Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ))) ≤ 0 := by
    have hc : (u i : ℝ) ≤ (u (i + 1) : ℝ) := by exact_mod_cast hmono i hi
    have hm := mul_le_mul_of_nonneg_left hc hq
    exact sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg hm))
  have hlast : Real.exp (-(q * (b : ℝ))) -
      Real.exp (-(q * (u n : ℝ))) ≤ 0 := by
    have hc : (u n : ℝ) ≤ (b : ℝ) := by exact_mod_cast hfinal
    have hm := mul_le_mul_of_nonneg_left hc hq
    exact sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg hm))
  have hsum : (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * f (i + 1)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonpos_of_nonneg (hneg i (Finset.mem_range.mp hi))
      (hf i (Finset.mem_range.mp hi))
  exact add_nonpos hsum (mul_nonpos_of_nonpos_of_nonneg hlast hfb)
