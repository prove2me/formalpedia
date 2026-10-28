-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_halfline_support_of_measure_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:48:11.97176+00:00
-- url     : https://prove2.me/submissions/2abb38c0-c6c4-423e-9d82-414dac37fb72

import Theorems.Thm_AvramDividend_Classical_positive_finite_supported_geometric_renewal_uniform
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Two measures supported on nonnegative reals have nonnegative-support convolution. -/
theorem solution
    (κ ν : Measure ℝ) [SFinite κ] [SFinite ν]
    (hκ : κ (Iio (0 : ℝ)) = 0)
    (hν : ν (Iio (0 : ℝ)) = 0) :
    (Measure.conv κ ν) (Iio (0 : ℝ)) = 0 := by
  have hκset : κ {x : ℝ | ¬ 0 ≤ x} = 0 := by
    have hs : {x : ℝ | ¬ 0 ≤ x} = Iio (0 : ℝ) := by ext x; simp
    rw [hs]; exact hκ
  have hνset : ν {y : ℝ | ¬ 0 ≤ y} = 0 := by
    have hs : {y : ℝ | ¬ 0 ≤ y} = Iio (0 : ℝ) := by ext y; simp
    rw [hs]; exact hν
  have hx : ∀ᵐ x : ℝ ∂κ, 0 ≤ x := (ae_iff).2 hκset
  have hy : ∀ᵐ y : ℝ ∂ν, 0 ≤ y := (ae_iff).2 hνset
  have hmeas : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 + p.2} := by
    measurability
  have hp : ∀ᵐ p : ℝ × ℝ ∂κ.prod ν, 0 ≤ p.1 + p.2 := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).2
    filter_upwards [hx] with x hx'
    filter_upwards [hy] with y hy'
    exact add_nonneg hx' hy'
  unfold Measure.conv
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hnull : (κ.prod ν) {p : ℝ × ℝ | p.1 + p.2 < 0} = 0 := by
    have hn := (ae_iff).mp hp
    simpa only [not_le] using hn
  exact hnull
