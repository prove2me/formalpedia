-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_upper_ae_fixed_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:57:13.572027+00:00
-- url     : https://prove2.me/submissions/d1aea463-b41d-4f89-849f-b0b76cf120cf

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_zero_probability
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Measure.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- At each fixed time, the actual BV Levy sample path is below its deterministic drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂P, X.X t ω ≤ (t : ℝ) * X.drift := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hnull (n : ℕ) :
      P {ω : Ω | (t : ℝ) * X.drift + 1 / ((n : ℝ) + 1) ≤ X.X t ω} = 0 := by
    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    exact (measureReal_eq_zero_iff).mp
      (bv_actual_levy_drift_upper_zero_probability
        X hBV t (1 / ((n : ℝ) + 1)) hε)
  have hsubset :
      {ω : Ω | (t : ℝ) * X.drift < X.X t ω} ⊆
      ⋃ n : ℕ, {ω : Ω |
        (t : ℝ) * X.drift + 1 / ((n : ℝ) + 1) ≤ X.X t ω} := by
    intro ω hω
    have hg : 0 < X.X t ω - (t : ℝ) * X.drift := sub_pos.mpr hω
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hg
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    change (t : ℝ) * X.drift + 1 / ((n : ℝ) + 1) ≤ X.X t ω
    linarith
  have hfull : P {ω : Ω | (t : ℝ) * X.drift < X.X t ω} = 0 :=
    measure_mono_null hsubset (measure_iUnion_null hnull)
  apply ae_iff.mpr
  simpa only [not_le] using hfull
