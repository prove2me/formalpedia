-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_source_continuous_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:31:39.202838+00:00
-- url     : https://prove2.me/submissions/35247f12-e2a5-4bbb-9952-9ff299e6a2e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_continuous_coefficients_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal source generator Gaussian and raw c-drift are discounted
L¹; epsilon=1 makes the annulus correction empty exactly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (clock : T → ℝ≥0) (w : ℝ → ℝ) (q : ℝ)
    (hder : Measurable (fun t => deriv w (R t)))
    (hhess : Measurable (fun t => iteratedDeriv 2 w (R t)))
    (hclock : Measurable clock)
    (hq : 0 ≤ q) (A : Set T) (hA : MeasurableSet A)
    (C : ℝ) (Cap : ℝ≥0∞) (u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hwCap : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hu : 0 < u) (hv : v < C)
    (hBand : Icc u v ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hcap : ∀ t ∈ A, R t ∈ Icc u v) :
    Integrable (A.indicator (fun t : T =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
          X.c * deriv w (R t)))) μ := by
  have h :=
    avram_p4_c_generator_discounted_finite_clock_continuous_coefficients_L1
      X μ R clock w q hder hhess hclock hq A hA
        C Cap u v 1 hw hwCap hu hv (by norm_num) hBand hcap
  simpa using h
