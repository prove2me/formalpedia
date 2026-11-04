-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_preruin_preterminal_drift_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:25:53.139923+00:00
-- url     : https://prove2.me/submissions/120cd75d-6a26-4c85-90d8-2b25a845b0b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (S : ℝ≥0) :
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D S ω ∧
      riskProcess X x D S ω ≤ x + (S : ℝ) * X.drift := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hmono
  intro hsurvive
  have hneg : 0 ≤ riskProcess X x D S ω :=
    riskProcess_nonnegative_strictly_before_ruin X x D ω S hsurvive
  have hres := hmono (show (0 : ℝ≥0) ≤ S from zero_le)
  have hpay : 0 ≤ D S ω := dividendStrategy_path_nonneg D hD ω S
  have hzero := hXzero ω
  constructor
  · exact hneg
  · change x + X.X S ω - D S ω ≤ x + (S : ℝ) * X.drift
    norm_num at hres
    rw [hzero] at hres
    linarith
