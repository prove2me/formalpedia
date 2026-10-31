-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_unconditional_gaussian_all_cap_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:04:01.879056+00:00
-- url     : https://prove2.me/submissions/81d7f578-ae6f-4ab9-960d-0cf45f64d7c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_all_cap_core_counterexample

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- A concrete Gaussian Lévy law refutes the UBV verification core at every cap. -/
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      ∀ (x : ℝ), 0 < x → x ≤ 1 →
      ∀ (C : ℝ≥0∞), ENNReal.ofReal x ≤ C →
      ∀ (T : ℝ), 0 ≤ T →
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    (X.Standing ∧ ¬ X.BoundedVariation ∧
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        1 ≤ deriv w y)) ∧
    IsAdmissibleLe X x C D ∧
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
  intro x hx hxle C hxc T hT
  exact avram_wave3_04_gaussian_all_cap_core_counterexample
    X (by rw [hσ]; norm_num) hI hν hc x hx hxle C hxc T hT