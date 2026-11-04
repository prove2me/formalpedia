-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_two_finite_measures_ae_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:34:18.324728+00:00
-- url     : https://prove2.me/submissions/09e38ddc-3ae2-400f-bdbd-ab78de8f8971

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_integral_uniform_error_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f g : Ω → ℝ)
    (hfμ : Integrable f μ) (hgμ : Integrable g μ)
    (hfν : Integrable f ν) (hgν : Integrable g ν)
    (δ : ℝ)
    (hδμ : ∀ᵐ ω ∂μ, |f ω - g ω| ≤ δ)
    (hδν : ∀ᵐ ω ∂ν, |f ω - g ω| ≤ δ) :
    |(∫ ω, f ω ∂μ) - (∫ ω, f ω ∂ν)| ≤
      |(∫ ω, g ω ∂μ) - (∫ ω, g ω ∂ν)| +
        δ * (μ.real Set.univ + ν.real Set.univ) := by
  let A : ℝ := ∫ ω, f ω ∂μ
  let B : ℝ := ∫ ω, f ω ∂ν
  let C : ℝ := ∫ ω, g ω ∂μ
  let D : ℝ := ∫ ω, g ω ∂ν
  have hμ : |A - C| ≤ δ * μ.real Set.univ := by
    exact AvramDividend.Classical.avram_p2_b_rate_finite_integral_uniform_error_bound
      μ f g hfμ hgμ δ hδμ
  have hν : |B - D| ≤ δ * ν.real Set.univ := by
    exact AvramDividend.Classical.avram_p2_b_rate_finite_integral_uniform_error_bound
      ν f g hfν hgν δ hδν
  have halg : A - B = (C - D) + (A - C) - (B - D) := by ring
  change |A - B| ≤ |C - D| + δ * (μ.real Set.univ + ν.real Set.univ)
  rw [halg]
  have hfirst : |(C - D) + (A - C) - (B - D)| ≤
      |(C - D) + (A - C)| + |B - D| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le ((C - D) + (A - C)) (-(B - D)))
  have hsecond : |(C - D) + (A - C)| ≤
      |C - D| + |A - C| := abs_add_le _ _
  nlinarith [hfirst, hsecond, hμ, hν]
