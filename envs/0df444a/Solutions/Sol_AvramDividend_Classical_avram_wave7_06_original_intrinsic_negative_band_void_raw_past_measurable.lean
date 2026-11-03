-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_raw_past_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:03:15.471207+00:00
-- url     : https://prove2.me/submissions/6001a02c-be8c-47b6-9774-c6b2118788a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_frozen_source_counter_rep_of_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_past_measurable_of_frozen_source_rep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual original-process negative-band voids belong to the original past filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    MeasurableSet[𝓕 T] {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hNX : ∀ ω : Ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
    intro ω
    rfl
  have hCad : ∀ ω : Ω,
      (∀ u : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
          (𝓝[<] u) (𝓝 l)) := by
    intro ω
    exact avram_wave7_06_original_frozen_prefix_cadlag_all_horizons X ω T
  obtain ⟨F, hF, hRep⟩ :=
    avram_wave7_06_original_negative_band_frozen_source_counter_rep_of_cadlag
      X T n hCad
  have hSource : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
        F (fun v : ℝ≥0 => X.X (min v T) ω) := by
    intro ω
    exact hRep ω
  have hPast :=
    avram_wave7_06_original_negative_band_past_measurable_of_frozen_source_rep
      X NX hNX T n F hF hSource
  simpa only [NX] using hPast
