-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_discount_cross_term_le_negative_contact_part
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:25:49.612583+00:00
-- url     : https://prove2.me/submissions/895e3613-4d36-47da-b2dd-75e07e049b70

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discount losses can contribute positively only where the post-cell value is negative. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (m : ℕ)
    (hmono : ∀ i, i < m + 1 → u i ≤ u (i + 1))
    (post : ℕ → ℝ) :
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * post (i + 1)) ≤
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) -
          Real.exp (-(q * (u (i + 1) : ℝ)))) * max (-post (i + 1)) 0) := by
  apply Finset.sum_le_sum
  intro i hi
  have hui : (u i : ℝ) ≤ (u (i + 1) : ℝ) :=
    NNReal.coe_le_coe.mpr (hmono i (Finset.mem_range.mp hi))
  have harg : -(q * (u (i + 1) : ℝ)) ≤ -(q * (u i : ℝ)) := by
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hui)]
  have hweight : 0 ≤ Real.exp (-(q * (u i : ℝ))) -
      Real.exp (-(q * (u (i + 1) : ℝ))) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr harg)
  calc
    (Real.exp (-(q * (u (i + 1) : ℝ))) -
      Real.exp (-(q * (u i : ℝ)))) * post (i + 1) =
      (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ)))) * (-post (i + 1)) := by ring
    _ ≤ (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ)))) *
          max (-post (i + 1)) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hweight
