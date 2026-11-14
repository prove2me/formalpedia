-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_physical_negative_mark_band_empty_under_compact_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T14:30:57.036093+00:00
-- url     : https://prove2.me/submissions/d3d10cd0-658e-41e4-b521-523382c776dc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The true source cannot jump into a negative nearzero band narrower than its compact mark gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hGap : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -δ)
    (n : ℕ) (hN : 1 / ((n : ℝ) + 1) < δ) :
    ∀ u : ℝ≥0, 0 < u → u ≤ T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∉
        Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ) := by
  intro u hu0 huT
  change ¬ (-(1 / ((n : ℝ) + 1)) <
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0)
  intro hBand
  have hNonzero :
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    linarith
  have hBound := hGap u hu0 huT hNonzero
  linarith
