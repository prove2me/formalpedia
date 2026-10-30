-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_real_clock_reflected_CDF_event_iff_lower_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:29:05.328082+00:00
-- url     : https://prove2.me/submissions/de204889-beff-4a6d-bee1-301e72b2f2b5

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact genuine original-Lévy random real-clock reflected CDF event is
the full uncountable-horizon lower-survival event, pathwise for each clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) :
    {z : Ω × ℝ |
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} =
    {z : Ω × ℝ |
      ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
        0 ≤ x + X.X s z.1} := by
  ext z
  exact chat04_reflected_infimum_Iic_iff_survival
    X (Real.toNNReal z.2) z.1 x
