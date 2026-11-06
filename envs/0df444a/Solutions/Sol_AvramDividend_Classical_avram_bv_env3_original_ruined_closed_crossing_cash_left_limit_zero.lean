-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_ruined_closed_crossing_cash_left_limit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:12:40.683504+00:00
-- url     : https://prove2.me/submissions/add218ee-7106-4fa9-96af-41bc660c6e85

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_closed_crossing_cash_left_limit_is_horizon_atom
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The ruin-clock original closed cash has zero full left-neighbourhood limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞))
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun a : ℝ =>
      ∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhdsWithin (T : ℝ) (Iio (T : ℝ))) (nhds 0) := by
  have hclosed :=
    avram_bv_env3_original_closed_crossing_cash_left_limit_is_horizon_atom
      D hD ω σ T q hq
  have hatom :=
    avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy
      D ω σ T hT hσ q
  simpa only [hatom] using hclosed
