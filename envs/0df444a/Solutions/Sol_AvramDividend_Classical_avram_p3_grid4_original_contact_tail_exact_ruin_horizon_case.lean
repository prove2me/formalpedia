-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_contact_tail_exact_ruin_horizon_case
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:07:11.410721+00:00
-- url     : https://prove2.me/submissions/cc2b0f0e-472d-4886-9e82-db0e2c47512d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_ruined_stopped_contact_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_contact_tail_cash_tendsto_exact_stop_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Resolve the actual original stopped contact cash on ruin and horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    0 < τ →
    Tendsto (fun m : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds (if ruinTime X x D ω = (τ : ℝ≥0∞) then 0
        else (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {(τ : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  change 0 < τ → _
  intro hτ
  by_cases hR : ruinTime X x D ω = (τ : ℝ≥0∞)
  · dsimp only [τ] at hR ⊢
    simpa only [if_pos hR] using
      (avram_p3_grid4_original_ruined_stopped_contact_tail_zero
        X x D hD ω T hT q hq hτ hR)
  · dsimp only [τ] at hR ⊢
    simpa only [if_neg hR] using
      (avram_p3_grid4_original_contact_tail_cash_tendsto_exact_stop_atom
        X x D hD ω T hT q hq hτ)
