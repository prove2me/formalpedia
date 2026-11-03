-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_empty_mark_predictable_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:34:04.593468+00:00
-- url     : https://prove2.me/submissions/20a6e1b1-849a-4d38-9d11-0f6e4325a1aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! Empty-mark exact predictable rectangle on the original source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (∅ : Set ℝ)) ∂P) =
    P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (∅ : Set ℝ) := by
  have hEmpty : Ioc s t ×ˢ (∅ : Set ℝ) = ∅ := by simp
  rw [hEmpty]
  simp
