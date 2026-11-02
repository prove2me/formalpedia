-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:22:00.461666+00:00
-- url     : https://prove2.me/submissions/1e62fd85-b6ad-4d26-bcfe-833dab5f2cad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Any original-sample random clock, clipped by a deterministic horizon,
leaves finitely many source jumps with magnitude bounded away from zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (τ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (min (τ ω) T) ×ˢ {y : ℝ | δ ≤ dist y 0}) < ⊤ := by
  have hfinite :=
    avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
      X ω T δ hδ
  have hsub :
      Ioc s (min (τ ω) T) ×ˢ {y : ℝ | δ ≤ dist y 0} ⊆
        Ioc 0 T ×ˢ {y : ℝ | δ ≤ dist y 0} := by
    intro p hp
    exact ⟨⟨lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hp.1.1,
      le_trans hp.1.2 (min_le_right (τ ω) T)⟩, hp.2⟩
  exact lt_of_le_of_lt (measure_mono hsub) hfinite
