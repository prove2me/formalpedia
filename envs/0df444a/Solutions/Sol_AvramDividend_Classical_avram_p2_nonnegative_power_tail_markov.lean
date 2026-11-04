-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_nonnegative_power_tail_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:00:03.640355+00:00
-- url     : https://prove2.me/submissions/fd807773-8de5-43a5-ba0b-9eca029988b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A positive-threshold polynomial moment controls the high-mark tail
of any real-valued measure, including original weighted Lévy images. -/
theorem solution
    (μ : MeasureTheory.Measure ℝ) (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    ENNReal.ofReal (R ^ k) * μ (Ici R) ≤
      ∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μ := by
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ k)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const k)
  have hsub :
      Ici R ⊆ {z : ℝ | ENNReal.ofReal (R ^ k) ≤ ENNReal.ofReal (z ^ k)} := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have hpow : R ^ k ≤ z ^ k := by
      gcongr
      exact hz
    exact hpow
  calc
    ENNReal.ofReal (R ^ k) * μ (Ici R) ≤
        ENNReal.ofReal (R ^ k) *
          μ {z : ℝ | ENNReal.ofReal (R ^ k) ≤ ENNReal.ofReal (z ^ k)} := by
      gcongr
    _ ≤ _ := mul_meas_ge_le_lintegral hm _
