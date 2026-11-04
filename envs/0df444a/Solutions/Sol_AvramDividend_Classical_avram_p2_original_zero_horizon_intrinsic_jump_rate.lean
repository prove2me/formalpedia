-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_zero_horizon_intrinsic_jump_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:48:27.252856+00:00
-- url     : https://prove2.me/submissions/cc7fc2cd-dd0a-4bfa-924a-3a3fd183a348

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The intrinsic jump measure of the original process charges no marks
in the empty positive-time interval when the horizon is zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (0 : ℝ≥0) ×ˢ B) ∂P) =
      (0 : ℝ≥0∞) * X.ν B := by
  simp
