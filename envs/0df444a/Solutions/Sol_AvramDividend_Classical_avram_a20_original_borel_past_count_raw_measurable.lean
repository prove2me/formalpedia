-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_past_count_raw_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:36:38.482511+00:00
-- url     : https://prove2.me/submissions/f8ef489e-a16d-43d2-8346-60de5dcee882

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_frozen_source_counter_rep_of_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)) := by
  classical
  have hCad (ω : Ω) :
      (∀ u : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
          (𝓝[<] u) (𝓝 l)) :=
    avram_wave7_06_original_frozen_prefix_cadlag_all_horizons X ω T
  obtain ⟨F, hF, hFrozen⟩ :=
    avram_a20_original_borel_frozen_source_counter_rep_of_cadlag
      X T B hB hCad
  have hCoordinate (v : ℝ≥0) :
      Measurable[𝓕 T] (fun ω : Ω => X.X (min v T) ω) := by
    exact (X.adapted (min v T)).mono
      (𝓕.mono (min_le_right v T)) le_rfl
  have hPath :
      Measurable[𝓕 T]
        (fun ω : Ω => (fun v : ℝ≥0 => X.X (min v T) ω)) := by
    letI : MeasurableSpace Ω := 𝓕 T
    exact measurable_pi_iff.mpr hCoordinate
  have hEq :
      (fun ω : Ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B)) =
      (fun ω : Ω => F (fun v : ℝ≥0 => X.X (min v T) ω)) := by
    funext ω
    exact hFrozen ω
  rw [hEq]
  exact hF.comp hPath
