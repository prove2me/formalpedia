-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_controlled_aggregate_loss_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:17:58.111026+00:00
-- url     : https://prove2.me/submissions/5af3e769-67d2-45dd-8c00-914d5d6b2c94

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 => (t : ℝ) * X.drift - riskProcess X x D t ω) := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hω
  intro s t hst
  have hsource := hω hst
  have hcontrol := hD.2.1 ω hst
  simp only [riskProcess] at *
  linarith only [hsource, hcontrol]
