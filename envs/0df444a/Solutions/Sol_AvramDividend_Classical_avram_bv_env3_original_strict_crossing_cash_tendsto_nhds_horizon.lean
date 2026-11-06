-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_strict_crossing_cash_tendsto_nhds_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:03:49.375064+00:00
-- url     : https://prove2.me/submissions/a635832c-2498-4e10-a1bf-f27b41a2fc98

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_oscillating_strict_crossing_cash_without_reference_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original strict crossing-cell cash tends to zero in the full real neighbourhood of T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun a : ℝ =>
      ∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhds (T : ℝ)) (nhds 0) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro a ha
  simpa only [Function.comp_def] using
    (avram_bv_env3_original_oscillating_strict_crossing_cash_without_reference_grid
      D hD ω σ T q hq a ha)
