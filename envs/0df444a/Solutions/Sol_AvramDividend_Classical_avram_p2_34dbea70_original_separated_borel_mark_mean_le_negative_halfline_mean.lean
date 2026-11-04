-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_separated_borel_mark_mean_le_negative_halfline_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:09:03.56571+00:00
-- url     : https://prove2.me/submissions/c9c71b30-9972-472d-90c2-6b17db11cdd6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A half-line moment envelope controls every separated negative Borel band. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (ε : ℝ) (hBsep : B ⊆ Iic (-ε)) (M : ℝ≥0∞)
    (hMean : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P) ≤ M) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) ≤ M := by
  calc
    _ ≤ (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P) := by
        apply lintegral_mono
        intro ω
        apply MeasureTheory.measure_mono
        intro x hx
        exact ⟨hx.1, hBsep hx.2⟩
    _ ≤ M := hMean
