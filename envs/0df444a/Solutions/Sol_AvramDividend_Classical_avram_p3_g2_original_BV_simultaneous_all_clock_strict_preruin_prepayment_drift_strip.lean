-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_BV_simultaneous_all_clock_strict_preruin_prepayment_drift_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:18:52.076069+00:00
-- url     : https://prove2.me/submissions/1f41ea9a-a68f-46fd-8dc5-9e60af1e7c37

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One full-probability source event bounds the actual prepayment reserve at
    every strictly pre-ruin real clock, including randomly chosen clocks.
    This strengthens fixed-horizon pointwise-a.e. strip bounds to all clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + (t : ℝ) * X.drift := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hmono
  intro t hsurvive
  have hnonneg : 0 ≤ riskProcess X x D t ω :=
    riskProcess_nonnegative_strictly_before_ruin X x D ω t hsurvive
  have hres := hmono (show (0 : ℝ≥0) ≤ t from zero_le)
  have hpay : 0 ≤ D t ω := dividendStrategy_path_nonneg D hD ω t
  have hzero := hXzero ω
  constructor
  · exact hnonneg
  · change x + X.X t ω - D t ω ≤ x + (t : ℝ) * X.drift
    norm_num at hres
    rw [hzero] at hres
    linarith
