-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_original_zero_trace_right_cash_le_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:43:09.309481+00:00
-- url     : https://prove2.me/submissions/9efee5f9-7308-4e63-9d92-387aaded3b45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-dividend cash between two zero postpayment reserves is drift dominated. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      x + X.X s ω - rightLimit D s ω = 0 →
      x + X.X t ω - rightLimit D t ω = 0 →
      rightLimit D t ω - rightLimit D s ω ≤
        ((t : ℝ) - (s : ℝ)) * X.drift := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hω
  intro s t hst hs ht
  have hmono := hω hst
  dsimp only at hmono
  nlinarith
