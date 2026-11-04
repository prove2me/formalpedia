-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_zero_horizon_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:36:31.070456+00:00
-- url     : https://prove2.me/submissions/88dc0953-80a8-4f80-adeb-e29115a5f8cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked count on a zero-length interval vanishes even
under arbitrary infinite ENNReal weights, with no jump-rate assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (B : Set ℝ) (H : Ω → ℝ≥0∞) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + 0) ×ˢ B) ∂P) = 0 := by
  have hRect : Ioc s (s + (0 : ℝ≥0)) ×ˢ B =
      (∅ : Set (ℝ≥0 × ℝ)) := by simp
  simp [hRect]
