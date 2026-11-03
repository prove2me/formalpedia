-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_arbitrary_borel_zero_duration_predictable_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:56:03.799835+00:00
-- url     : https://prove2.me/submissions/a0c066e2-5cf2-4b87-bc0e-d0f15a6d0ad2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Full original-process predictable rectangle equality on a zero-length interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s s ×ˢ B) ∂P) =
    P A * (((s - s : ℝ≥0) : ℝ≥0∞)) * X.ν B := by
  classical
  simp
