-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_ruined_horizon_closed_crossing_cash_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:22:19.439166+00:00
-- url     : https://prove2.me/submissions/87d60dfe-0691-48e4-80cf-e952065268af

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_stopped_clock_horizon_payment_atom_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At a positive horizon after ruin, the closed final-cell cash also vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞))
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Monotone a)
    (hlim : Tendsto a atTop (nhds (T : ℝ)))
    (hbelow : ∀ n, a n < (T : ℝ)) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  have hAtom :=
    avram_bv_env3_original_stopped_clock_horizon_payment_atom_zero
      D hD ω σ T hT hσ q
  have hLimit :=
    avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
      D hD ω σ T q hq a ha hlim hbelow
  simpa only [hAtom] using hLimit
