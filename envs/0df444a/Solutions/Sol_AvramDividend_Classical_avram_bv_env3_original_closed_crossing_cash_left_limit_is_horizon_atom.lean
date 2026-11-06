-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_closed_crossing_cash_left_limit_is_horizon_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:10:24.270212+00:00
-- url     : https://prove2.me/submissions/e918cbcc-6e54-4d51-9b77-9c5c4c7524d2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_crossing_cash_tendsto_nhds_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original closed crossing-cell cash has the exact horizon atom as its left limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun a : ℝ =>
      ∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhdsWithin (T : ℝ) (Iio (T : ℝ)))
      (nhds (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  have hstrict :=
    avram_bv_env3_original_strict_crossing_cash_tendsto_nhds_horizon
      D hD ω σ T q hq
  have hstrictWithin : Tendsto
      (fun a : ℝ => ∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhdsWithin (T : ℝ) (Iio (T : ℝ))) (nhds 0) := by
    exact hstrict.mono_left inf_le_left
  have hconst : Tendsto
      (fun _ : ℝ => ∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhdsWithin (T : ℝ) (Iio (T : ℝ)))
      (nhds (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) :=
    tendsto_const_nhds
  have hplus := hstrictWithin.add hconst
  have hclosed := hplus.congr' (by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
      D hD ω σ T q a ha).symm)
  simpa only [zero_add] using hclosed
