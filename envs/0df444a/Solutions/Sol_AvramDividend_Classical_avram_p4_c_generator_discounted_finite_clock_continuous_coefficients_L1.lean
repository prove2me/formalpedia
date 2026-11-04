-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_continuous_coefficients_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:16:10.086857+00:00
-- url     : https://prove2.me/submissions/201ecb37-0d27-4eba-8e56-579d8f1877a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_physical_drift_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal original Gaussian and epsilon-renormalised physical drift
are jointly discounted L¹ on finite compact-interior observation clocks. -/
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
    (C : ℝ) (Cap : ℝ≥0∞) (u v ε : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hwCap : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hu : 0 < u) (hv : v < C) (hε : 0 < ε)
    (hBand : Icc u v ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hcap : ∀ t ∈ A, R t ∈ Icc u v) :
    Integrable (A.indicator (fun t : T =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
         (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (R t)))) μ := by
  classical
  obtain ⟨K, hKnonneg, hK⟩ :=
    avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
      X q hq Cap w hwCap u v hBand
  let gauss : T → ℝ := fun t => Real.exp (-(q * (clock t : ℝ))) *
    (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t))
  have hgmeas : Measurable gauss := by
    dsimp [gauss]
    fun_prop
  have hgint : Integrable (A.indicator gauss) μ := by
    apply (integrable_const K).mono' (hgmeas.indicator hA).aestronglyMeasurable
    filter_upwards [] with t
    by_cases ht : t ∈ A
    · simpa only [Set.indicator_of_mem ht, Real.norm_eq_abs, gauss] using
        hK (clock t) (R t) (hcap t ht)
    · simp [Set.indicator, ht, hKnonneg]
  have hctime : Measurable (fun t : T => (clock t : ℝ)) := by
    fun_prop
  have hctimepos : ∀ t : T, 0 ≤ (clock t : ℝ) := by
    intro t
    exact (clock t).property
  have hdint :=
    avram_p4_c_generator_discounted_finite_clock_physical_drift_L1
      X μ R (fun t : T => (clock t : ℝ)) w q
        hder hctime hctimepos hq A hA C u v ε hw hu hv hε hcap
  let drift : T → ℝ := fun t => Real.exp (-(q * (clock t : ℝ))) *
    ((X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (R t))
  have hsum :
      A.indicator (fun t : T => Real.exp (-(q * (clock t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
          (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (R t))) =
      (fun t => A.indicator gauss t + A.indicator drift t) := by
    funext t
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht, gauss, drift, mul_add]
    · simp [Set.indicator, ht]
  rw [hsum]
  exact hgint.add hdint
