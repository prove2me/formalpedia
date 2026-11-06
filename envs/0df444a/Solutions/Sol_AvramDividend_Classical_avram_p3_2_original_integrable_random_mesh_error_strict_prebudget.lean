-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_integrable_random_mesh_error_strict_prebudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:06:13.398214+00:00
-- url     : https://prove2.me/submissions/bf2a25fb-157a-433f-983e-bef9c8469476

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_vanishing_error_grid_to_actual_prebudget_direct

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Integrable random original-X/D finite-grid errors with vanishing
mean can be centred into signed residuals before physical Fatou passage. -/
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
    (hFInt : ∀ n, Integrable (F n) P)
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
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => ∫ ω, Err n ω ∂P
  let Signed : ℕ → Ω → ℝ := fun n ω => R n ω + Err n ω - δ n
  have hSigned (n : ℕ) :
      Integrable (Signed n) P ∧
        (∫ ω, Signed n ω ∂P) ≤ 0 := by
    constructor
    · exact ((hR n).1.add (hErrInt n)).sub (integrable_const _)
    · have hIntegral : (∫ ω, Signed n ω ∂P) =
          (∫ ω, R n ω ∂P) := by
        change (∫ ω, (R n + Err n) ω - (fun _ : Ω => δ n) ω ∂P) =
          (∫ ω, R n ω ∂P)
        rw [integral_sub ((hR n).1.add (hErrInt n))
          (integrable_const (δ n))]
        simp only [Pi.add_apply]
        rw [integral_add (hR n).1 (hErrInt n)]
        simp [δ]
      rw [hIntegral]
      exact (hR n).2
  have hBoundSigned (n : ℕ) :
      ∀ᵐ ω ∂P,
        F n ω ≤ w x + Signed n ω + δ n := by
    filter_upwards [hBound n] with ω hω
    dsimp [Signed, δ]
    linarith only [hω]
  have hδ : Tendsto δ atTop (nhds (0 : ℝ)) := hErrMean
  exact avram_p3_2_original_vanishing_error_grid_to_actual_prebudget_direct
    X hBV x C D hD w hw_cont hw_neg hw_nonneg
    q hq T hT hTpos F Signed δ hFMeas hFInt
    hFNonneg hSigned hδ hBoundSigned hFatou
