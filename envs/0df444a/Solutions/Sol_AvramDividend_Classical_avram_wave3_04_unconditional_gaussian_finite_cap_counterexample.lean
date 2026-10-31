-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_unconditional_gaussian_finite_cap_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:54:16.471867+00:00
-- url     : https://prove2.me/submissions/a42ec421-1839-4006-9143-28818cfc58a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_finite_cap_core_counterexample

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- A concrete Gaussian Lévy law refutes the UBV verification core at finite cap one. -/
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      ∀ (x : ℝ), 0 < x → x ≤ 1 → ∀ (T : ℝ), 0 ≤ T →
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    (X.Standing ∧ ¬ X.BoundedVariation ∧
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ)} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
        1 ≤ deriv w y)) ∧
    ENNReal.ofReal x ≤ ENNReal.ofReal (1 : ℝ) ∧
    IsAdmissibleLe X x (ENNReal.ofReal (1 : ℝ)) D ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) ∧
    ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-((1 : ℝ) * t)))
        ∂(dividendMeasure D ω) ∂gaussianLimit) ≤ ENNReal.ofReal (w x)) := by
  obtain ⟨𝓕, X, hX, hc, hσ, hν⟩ :=
    avram_wave3_04_concrete_gaussian_levy_source_witness
  have hI : Integrable (X.X 1) gaussianLimit := by
    rw [hX]
    exact avram_wave3_04_gaussian_drifted_unit_integrable
  refine ⟨𝓕, X, ?_⟩
  intro x hx hxle T hT
  exact avram_wave3_04_gaussian_finite_cap_core_counterexample
    X (by rw [hσ]; norm_num) hI hν hc x hx hxle T hT