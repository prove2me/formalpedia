-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:59:45.036208+00:00
-- url     : https://prove2.me/submissions/ff7fc730-04a9-4295-9869-49986176eb8f

import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_positive_compact_intensity_eq_nu_tests_v3
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_signed_compact_test_eq_of_positive_lintegrals
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original nonnegative compact-test rates extend to all signed compact-negative tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ σ : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * σ B) ∧
      (∀ (f : ℝ → ℝ), Continuous f → IsCompact (tsupport f) →
        tsupport f ⊆ Iio (0 : ℝ) →
        (∫ y, f y ∂σ) =
          (∫ y, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) ∧
      (∀ ε : ℝ, 0 < ε → σ (Iic (-ε)) < ⊤) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        σ B = σ (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite σ := by
  obtain ⟨σ, hRate, hPos, hBand, hSupport, hSF⟩ :=
    avram_p2_a_assist_original_positive_compact_intensity_eq_nu_tests_v3 P X
  refine ⟨σ, hRate, ?_, hBand, hSupport, hSF⟩
  have hνBand : ∀ ε : ℝ, 0 < ε →
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-ε)) < ⊤ := by
    intro ε hε
    have hsep : Iic (-ε) ⊆ Iio (0 : ℝ) := by
      intro y hy
      have hy' : y ≤ -ε := hy
      change y < 0
      linarith
    have hνfin : X.ν (Iic (-ε)) < ⊤ :=
      avram_p2_a_zero_rate_separated_borel_nu_finite
        X (Iic (-ε)) measurableSet_Iic ε hε Subset.rfl
    calc
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-ε)) =
          X.ν (Iic (-ε) ∩ Iio (0 : ℝ)) :=
            Measure.restrict_apply measurableSet_Iic
      _ = X.ν (Iic (-ε)) :=
        congrArg X.ν (inter_eq_left.mpr hsep)
      _ < ⊤ := hνfin
  have hInt : ∀ f : ℝ → ℝ, Continuous f → IsCompact (tsupport f) →
      tsupport f ⊆ Iio (0 : ℝ) → (∀ x : ℝ, 0 ≤ f x) →
      Integrable f σ ∧ Integrable f (X.ν.restrict (Iio (0 : ℝ))) := by
    intro f hf hc hneg _
    exact ⟨avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
        σ hBand f hf hc hneg,
      avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
        _ hνBand f hf hc hneg⟩
  have hPosLin : ∀ f : ℝ → ℝ, Continuous f → IsCompact (tsupport f) →
      tsupport f ⊆ Iio (0 : ℝ) → (∀ x : ℝ, 0 ≤ f x) →
      (∫⁻ y, ENNReal.ofReal (f y) ∂σ) =
        (∫⁻ y, ENNReal.ofReal (f y) ∂(X.ν.restrict (Iio (0 : ℝ)))) := by
    intro f hf hc hneg hnonneg
    have hνInt := (hInt f hf hc hneg hnonneg).2
    exact (hPos f hf hc hneg hnonneg).trans
      (ofReal_integral_eq_lintegral_ofReal hνInt
        (Filter.Eventually.of_forall hnonneg))
  intro f hf hc hneg
  exact avram_p2_a_zero_rate_signed_compact_test_eq_of_positive_lintegrals
    σ (X.ν.restrict (Iio (0 : ℝ))) hInt hPosLin f hf hc hneg
