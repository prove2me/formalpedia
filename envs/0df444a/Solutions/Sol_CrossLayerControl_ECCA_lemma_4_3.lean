-- Prove2me | solution 1 for CrossLayerControl.ECCA.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:38:56.870982+00:00
-- url     : https://prove2.me/submissions/d5c3a2e9-f69f-4e10-9c23-f1799b2810e4

import Mathlib

theorem solution (W U μ A : ℝ) (hW : 0 ≤ W) (hU : 0 ≤ U) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (h : W ≤ max (U - μ) 0 + A) :
    W ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) := by
  have hsq : W ^ 2 ≤ (max (U - μ) 0 + A) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hW h
  by_cases hμU : μ ≤ U
  · have hmax : max (U - μ) 0 = U - μ := max_eq_left (sub_nonneg.mpr hμU)
    rw [hmax] at hsq
    have hpoly : (U - μ + A) ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) := by
      nlinarith
    exact le_trans hsq hpoly
  · have hmax : max (U - μ) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge hμU))
    rw [hmax, zero_add] at hsq
    have hpoly : A ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) := by
      nlinarith
    exact le_trans hsq hpoly
