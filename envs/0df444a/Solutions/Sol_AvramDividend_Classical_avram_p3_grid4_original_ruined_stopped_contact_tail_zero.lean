-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_ruined_stopped_contact_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:52:33.89229+00:00
-- url     : https://prove2.me/submissions/2652e750-651a-4a71-b344-63956a15a394

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_approach_certificate
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_ruined_horizon_closed_crossing_cash_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original positive ruin contact tail has no surviving right-closed payment mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    0 < τ → ruinTime X x D ω = (τ : ℝ≥0∞) →
    Tendsto (fun m : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  change 0 < τ → ruinTime X x D ω = (τ : ℝ≥0∞) → _
  intro hτ hStop
  obtain ⟨ha, hlim, hbelow⟩ :=
    avram_p3_grid4_contact_left_endpoint_approach_certificate τ T hτ hT
  have hσ : ruinTime X x D ω ≤ (τ : ℝ≥0∞) := le_of_eq hStop
  simpa only using
    (avram_bv_env3_original_ruined_horizon_closed_crossing_cash_tendsto_zero
      D hD ω (ruinTime X x D ω) τ hτ hσ q hq
      (fun m : ℕ => ((τ - T / (m + 1) : ℝ≥0) : ℝ))
      ha hlim hbelow)
