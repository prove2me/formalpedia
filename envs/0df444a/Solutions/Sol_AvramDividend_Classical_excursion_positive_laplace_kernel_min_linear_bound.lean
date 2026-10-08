-- Prove2me | solution 1 for AvramDividend.Classical.excursion_positive_laplace_kernel_min_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:32:42.774294+00:00
-- url     : https://prove2.me/submissions/7a9cf41a-8637-4512-b36b-3e152c6edc9f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (s t : ℝ) (hs : 1 ≤ s) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-(s * t)) ∧
      1 - Real.exp (-(s * t)) ≤ s * min 1 t := by
  have hs0 : 0 ≤ s := by linarith
  have hst : 0 ≤ s * t := mul_nonneg hs0 ht
  have hnonneg : 0 ≤ 1 - Real.exp (-(s * t)) := by
    exact sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hst))
  have htangent : 1 - Real.exp (-(s * t)) ≤ s * t := by
    have h := Real.add_one_le_exp (-(s * t))
    linarith
  refine ⟨hnonneg, ?_⟩
  rcases le_total t 1 with hsmall | hlarge
  · rw [min_eq_right hsmall]
    exact htangent
  · rw [min_eq_left hlarge, mul_one]
    have hnon : 0 ≤ Real.exp (-(s * t)) := (Real.exp_pos _).le
    linarith
