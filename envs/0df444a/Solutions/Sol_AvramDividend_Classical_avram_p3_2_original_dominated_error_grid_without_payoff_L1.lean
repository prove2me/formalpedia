-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_dominated_error_grid_without_payoff_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:53:24.684023+00:00
-- url     : https://prove2.me/submissions/61334b9d-6cfc-4ec1-b076-8882d5fc53de

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_dominated_random_mesh_error_strict_prebudget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive original physical-grid rewards controlled by an integrable
compensator plus an integrable error are themselves L1. The error has zero
limiting expectation by dominated convergence; Fatou gives the exact reward. -/
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
    (H : Ω → ℝ) (hHInt : Integrable H P)
    (hDom : ∀ n, ∀ᵐ ω ∂P, ‖Err n ω‖ ≤ H ω)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => Err n ω) atTop (nhds (0 : ℝ)))
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
  have hFInt : ∀ n, Integrable (F n) P := by
    intro n
    have hTop : Integrable
        (fun ω => (w x + R n ω) + Err n ω) P :=
      ((integrable_const (w x)).add (hR n).1).add (hErrInt n)
    have hNorm : ∀ᵐ ω ∂P,
        ‖F n ω‖ ≤ (w x + R n ω) + Err n ω := by
      filter_upwards [hFNonneg n, hBound n] with ω hnon hupper
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnon] using hupper
    exact hTop.mono' (hFMeas n).aestronglyMeasurable hNorm
  exact avram_p3_2_original_dominated_random_mesh_error_strict_prebudget
    X hBV x C D hD w hw_cont hw_neg hw_nonneg
    q hq T hT hTpos F R Err hFMeas hFInt hFNonneg
    hR hErrInt H hHInt hDom hErrAE hBound hFatou
