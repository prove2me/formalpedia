-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_empty_band_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:33:58.028432+00:00
-- url     : https://prove2.me/submissions/56017253-6859-4447-bd81-b083fab09d2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked count assigns zero to an empty mark set at
all nonnegative times, including infinite-activity sample paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
         X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc 0 T ×ˢ (∅ : Set ℝ)) ∂P) = 0 := by
  simp
