-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:18:48.666207+00:00
-- url     : https://prove2.me/submissions/3801b860-e0c7-4879-be51-5a1fa31004e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_vanishing_error_grid_to_actual_prebudget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Assemble the exact original P3 two-correction signed Fatou grid into its
    stopped strict expected prebudget, with zero deterministic mesh error. -/
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
    (hGrid : ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  obtain ⟨F, M, B, hFMeas, hFInt, hFPos, hMB, hGridBound, hFatou⟩ := hGrid
  let R : ℕ → Ω → ℝ := fun n ω => M n ω + B n ω
  have hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0 := by
    intro n
    simpa only [R] using hMB n
  have hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + R n ω + (0 : ℝ) := by
    intro n
    filter_upwards [hGridBound n] with ω hω
    simpa only [R, add_zero] using hω
  have hZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (nhds (0 : ℝ)) := tendsto_const_nhds
  exact avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
    X hBV x C D hD w hw_cont hw_neg hw_nonneg
    q hq T hT hTpos F R (fun _ => 0)
    hFMeas hFInt hFPos hR hZero hBound hFatou
