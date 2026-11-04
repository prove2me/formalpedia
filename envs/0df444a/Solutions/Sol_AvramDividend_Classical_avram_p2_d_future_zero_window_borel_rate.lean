-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_zero_window_borel_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:52:47.449605+00:00
-- url     : https://prove2.me/submissions/dfe6072b-410f-4c2a-ac2e-eea621836ed1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original zero-duration marked window has zero sample count and the
rate identity holds even if the original Levy intensity is infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (B : Set ℝ) :
    (∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s s ×ˢ B) = 0) ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s s ×ˢ B) ∂P) =
    ((s - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  constructor
  · intro ω
    simp
  · simp
