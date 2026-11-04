-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_monotone_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:56:43.440316+00:00
-- url     : https://prove2.me/submissions/b9d15a25-b259-4e63-a26b-6acfb766a2a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual intrinsic marked-jump expectation is monotone in the mark set. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B C : Set ℝ) (hBC : B ⊆ C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) ≤
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ C) ∂P) := by
  apply lintegral_mono
  intro ω
  apply MeasureTheory.measure_mono
  intro p hp
  exact ⟨hp.1, hBC hp.2⟩
