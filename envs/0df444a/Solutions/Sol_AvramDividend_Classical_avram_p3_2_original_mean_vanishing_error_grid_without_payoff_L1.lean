-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_mean_vanishing_error_grid_without_payoff_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:05:30.218724+00:00
-- url     : https://prove2.me/submissions/fd534c06-d9d8-4fe5-bac6-d5c6b34d425f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_fatou_grid_integrability_from_signed_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_integrable_random_mesh_error_strict_prebudget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original-grid random errors need only vanishing expectation;
the integrability of nonnegative physical rewards follows from their
signed integrable upper bound, with no global error dominator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (F R Err : ℕ → Ω → ℝ)
    (hFMeas : ∀ n, Measurable (F n))
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (Err n) P)
    (hErrMean : Tendsto (fun n => ∫ ω, Err n ω ∂P)
      atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + R n ω + Err n ω)
    (hFatou : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  have hSigned : ∀ n,
      Integrable (fun ω => R n ω + Err n ω) P := by
    intro n
    exact (hR n).1.add (hErrInt n)
  have hBound' : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (R n ω + Err n ω) := by
    intro n
    filter_upwards [hBound n] with ω hω
    linarith
  have hFInt : ∀ n, Integrable (F n) P :=
    avram_p3_2_original_fatou_grid_integrability_from_signed_upper
      X hBV x C D hD w F R Err
      hFMeas hFNonneg hSigned hBound'
  exact avram_p3_2_original_integrable_random_mesh_error_strict_prebudget
    X hBV x C D hD w hw_cont hw_neg hw_nonneg
    q hq T hT hTpos F R Err hFMeas hFInt hFNonneg
    hR hErrInt hErrMean hBound hFatou
