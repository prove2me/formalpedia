-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep7_original_strict_fatou_from_signed_grid_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:08:35.821256+00:00
-- url     : https://prove2.me/submissions/bfedba9f-39e8-49e6-b63f-643d0e6c093b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_strict_stopped_fatou_expected_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hwx : 0 ≤ w x)
    (F M B : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hMesh : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω))
    (hLiminf : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBudget (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal (w x) := by
    obtain ⟨hSInt, hSMean⟩ := hSigned n
    have hSumEq :
        (∫ ω, w x + (M n ω + B n ω) ∂P) =
          w x + (∫ ω, M n ω + B n ω ∂P) := by
      rw [integral_add (integrable_const _) hSInt]
      simp
    have hComp :
        (∫ ω, F n ω ∂P) ≤
          (∫ ω, w x + (M n ω + B n ω) ∂P) :=
      integral_mono_ae (hFint n)
        ((integrable_const _).add hSInt) (hMesh n)
    have hMean : (∫ ω, F n ω ∂P) ≤ w x := by
      rw [hSumEq] at hComp
      linarith
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hFint n) (hFnonneg n)]
    exact ENNReal.ofReal_mono hMean
  exact avram_p3_main_original_strict_stopped_fatou_expected_budget
    X hBV x C D hD w hw_cont hw_neg q hq T hT hTpos
    hw_nonneg hwx (fun n ω => ENNReal.ofReal (F n ω))
    (fun n => ENNReal.continuous_ofReal.measurable.comp (hFmeas n))
    hLiminf hBudget
