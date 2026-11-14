-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a155_original_gaussian_fullcell_discount_source_width_energy_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:30:35.212706+00:00
-- url     : https://prove2.me/submissions/f7a8ffb0-ff7f-4f4e-aec1-823dba2a38b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- Original full source discount-width weighted Gaussian absolute increments are controlled by exact physical quadratic energy. -/
theorem solution
    (m : ℕ) (R : ℕ → ℝ) (q Δ L K : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hE : (∑ i ∈ Finset.range m, (R i)^2) ≤ K) :
    (q * Δ * L * (∑ i ∈ Finset.range m, |R i|))^2 ≤
      (q * Δ * L)^2 * ((m : ℝ) * K) := by
  have hCS : (∑ i ∈ Finset.range m, |R i|)^2 ≤
      (m : ℝ) * (∑ i ∈ Finset.range m, (R i)^2) := by
    simpa only [Finset.card_range, sq_abs] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range m) (f := fun i => |R i|))
  have hM : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hSquare : (∑ i ∈ Finset.range m, |R i|)^2 ≤ (m : ℝ) * K := by
    exact hCS.trans (mul_le_mul_of_nonneg_left hE hM)
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hSquare (sq_nonneg (q * Δ * L))
