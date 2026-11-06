-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_ruined_oscillating_closed_crossing_cash_without_reference_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:57:57.419389+00:00
-- url     : https://prove2.me/submissions/b29473f1-7696-40c1-a04b-feea581b89f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_oscillating_closed_crossing_cash_without_reference_grid
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_stopped_clock_horizon_payment_atom_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On a ruin path by T, the stopped payment clock eliminates the horizon
    atom left over by an arbitrarily oscillating last-cell grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞))
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ)))
    (hbelow : ∀ n, a n < (T : ℝ)) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  have hclosed :=
    avram_bv_env3_original_oscillating_closed_crossing_cash_without_reference_grid
      D hD ω σ T q hq a ha hbelow
  have hatom :=
    avram_bv_env3_original_stopped_clock_horizon_payment_atom_zero
      D hD ω σ T hT hσ q
  simpa only [hatom] using hclosed
