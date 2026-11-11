-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger60_gaussian_scalar_HJB_one_sided_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:24:00.626365+00:00
-- url     : https://prove2.me/submissions/49a99030-6de4-49ac-b3fe-68fca7b92924

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger56_discounted_gaussian_characteristic_roots
import Theorems.Thm_AvramDividend_Classical_avram_gledger57_weighted_first_derivative_one_sided_exponential_envelope
import Theorems.Thm_AvramDividend_Classical_avram_gledger58_factorised_second_order_ode_weighted_first_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- The Gaussian scalar HJB upper inequality gives a one-sided positive-tail
    exponential envelope, with no control imposed on the negative tail. -/
theorem solution
    (a b q u : ℝ) (ha : 0 < a) (hq : 0 < q) (hu : 0 < u)
    (w : ℝ → ℝ)
    (hsmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hode : ∀ y : ℝ, 0 < y →
      a * iteratedDeriv 2 w y + b * deriv w y - q * w y ≤ 0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, u ≤ y → w y ≤ K * Real.exp (θ * y) := by
  obtain ⟨r, l, hr, hl, hlin, hprod⟩ :=
    avram_gledger56_discounted_gaussian_characteristic_roots a b q ha hq
  have hrl : l < r := lt_trans hl hr
  have hw (y : ℝ) (hy : u ≤ y) :
      HasDerivAt w (deriv w y) y :=
    (hsmooth y (lt_of_lt_of_le hu hy)).1
  have hw2 (y : ℝ) (hy : u ≤ y) :
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y :=
    (hsmooth y (lt_of_lt_of_le hu hy)).2
  have hfact (y : ℝ) (hy : u ≤ y) :
      iteratedDeriv 2 w y - (r + l) * deriv w y +
        r * l * w y ≤ 0 := by
    have hg := hode y (lt_of_lt_of_le hu hy)
    have heq :
        a * (iteratedDeriv 2 w y - (r + l) * deriv w y +
          r * l * w y) =
        a * iteratedDeriv 2 w y + b * deriv w y - q * w y := by
      rw [hlin, hprod]
      ring
    rw [← heq] at hg
    by_contra hnot
    have hpos : 0 < iteratedDeriv 2 w y - (r + l) * deriv w y +
        r * l * w y := lt_of_not_ge hnot
    exact (not_le_of_gt (mul_pos ha hpos)) hg
  have hweighted :=
    avram_gledger58_factorised_second_order_ode_weighted_first_derivative
      r l u w hw hw2 hfact
  obtain ⟨K, hK, hbound⟩ :=
    avram_gledger57_weighted_first_derivative_one_sided_exponential_envelope
      r l u hrl hu w hw hweighted
  exact ⟨r, K, le_of_lt hr, hK, hbound⟩
