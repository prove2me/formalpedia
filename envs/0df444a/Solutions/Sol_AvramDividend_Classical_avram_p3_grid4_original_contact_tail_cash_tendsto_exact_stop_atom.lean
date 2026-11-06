-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_contact_tail_cash_tendsto_exact_stop_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:11:55.013639+00:00
-- url     : https://prove2.me/submissions/8d6c41df-2fa6-4ba8-858b-0fcc95573791

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_approach_certificate
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original crossing-tail cash approaches exactly its true stopped singleton atom. -/
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
      atTop (nhds
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {(τ : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  change 0 < τ → _
  intro hτ
  have hApproach :=
    avram_p3_grid4_contact_left_endpoint_approach_certificate τ T hτ hT
  rcases hApproach with ⟨ha, hlim, hbelow⟩
  simpa only using
    (avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
      D hD ω (ruinTime X x D ω) τ q hq
      (fun m : ℕ => ((τ - T / (m + 1) : ℝ≥0) : ℝ))
      ha hlim hbelow)
