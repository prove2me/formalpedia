-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_global_postpayment_upper_horizon_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:41:17.60113+00:00
-- url     : https://prove2.me/submissions/0ecee768-6b2b-4285-b4f1-49d6b39e73ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV controlled reserve has a global upper horizon strip, even beyond ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      x + X.X t ω - rightLimit D t ω ≤
        x + max ((T : ℝ) * X.drift) 0 := by
  filter_upwards
    [avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
      X hBV x D hD] with ω hInc
  intro t ht
  have hD0 : 0 ≤ rightLimit D 0 ω := by
    calc
      0 = D 0 ω := (hD.1 ω).symm
      _ ≤ rightLimit D 0 ω := dividendStrategy_le_rightLimit D hD ω 0
  have hTime : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hStep : (t : ℝ) * X.drift ≤ max ((T : ℝ) * X.drift) 0 := by
    by_cases hd : 0 ≤ X.drift
    · exact (mul_le_mul_of_nonneg_right hTime hd).trans (le_max_left _ _)
    · have hdneg : X.drift ≤ 0 := le_of_not_ge hd
      have ht0 : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
      exact (mul_nonpos_of_nonneg_of_nonpos ht0 hdneg).trans
        (le_max_right _ _)
  have hInc0 := hInc 0 t (show (0 : ℝ≥0) ≤ t from zero_le)
  rw [X.X_zero ω] at hInc0
  norm_num at hInc0
  linarith
