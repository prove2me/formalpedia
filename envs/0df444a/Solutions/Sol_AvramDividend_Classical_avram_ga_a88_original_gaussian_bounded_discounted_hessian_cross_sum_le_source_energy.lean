-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a88_original_gaussian_bounded_discounted_hessian_cross_sum_le_source_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:45:30.857184+00:00
-- url     : https://prove2.me/submissions/0dae4713-2915-4814-a108-aedf590344ca

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A bounded original discounted Gaussian Hessian controls every physical-grid raw-centred quadratic cross error. -/
theorem solution (S : Finset ℕ) (H R : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ i ∈ S, |H i| ≤ K) :
    |∑ i ∈ S, H i / 2 * R i| ≤
      (K / 2) * ∑ i ∈ S, |R i| := by
  have hPoint (i : ℕ) (hi : i ∈ S) :
      |H i / 2 * R i| ≤ (K / 2) * |R i| := by
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg (R i))
    exact div_le_div_of_nonneg_right (hH i hi) (by norm_num)
  calc
    |∑ i ∈ S, H i / 2 * R i| ≤
        ∑ i ∈ S, |H i / 2 * R i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, (K / 2) * |R i| :=
      Finset.sum_le_sum hPoint
    _ = (K / 2) * ∑ i ∈ S, |R i| :=
      by rw [Finset.mul_sum]
