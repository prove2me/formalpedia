-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_zero_horizon_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:31:34.394356+00:00
-- url     : https://prove2.me/submissions/8b69d216-663a-4242-b27b-9817f239965c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked jump count is identically zero on the empty
positive-time interval, so its ENNReal expectation vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
         X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc 0 0 ×ˢ B) ∂P) = 0 := by
  simp
