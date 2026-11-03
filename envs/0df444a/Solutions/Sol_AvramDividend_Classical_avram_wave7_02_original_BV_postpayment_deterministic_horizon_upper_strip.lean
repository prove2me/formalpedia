-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:29:33.997284+00:00
-- url     : https://prove2.me/submissions/d8c8b13b-d0c3-4050-9de8-827baf9cf36e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original BV postpayment reserve has a deterministic upward horizon envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hd : 0 ≤ X.drift) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), t ≤ T →
      x + X.X t ω - rightLimit D t ω ≤
        x + (T : ℝ) * X.drift := by
  filter_upwards
    [avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
      X hBV x D hD] with ω hInc
  intro t ht
  have hD0 : 0 ≤ rightLimit D 0 ω := by
    calc
      0 = D 0 ω := (hD.1 ω).symm
      _ ≤ rightLimit D 0 ω := dividendStrategy_le_rightLimit D hD ω 0
  have hTime : (t : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast ht
  have hStep : (t : ℝ) * X.drift ≤ (T : ℝ) * X.drift :=
    mul_le_mul_of_nonneg_right hTime hd
  have hInc0 := hInc 0 t (show (0 : ℝ≥0) ≤ t from zero_le)
  rw [X.X_zero ω] at hInc0
  norm_num at hInc0
  linarith
