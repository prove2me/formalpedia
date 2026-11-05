-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_window_count_finset_filter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:26:54.091387+00:00
-- url     : https://prove2.me/submissions/a3374c08-7ed1-4140-af35-899ae057dd73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original source window counts filter the actual full-horizon finite jump-time set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    (((avram_wave7_06_original_negative_band_marked_times_finite
      X ω T n).toFinset.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by
  classical
  let F : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}
  let S : Set ℝ≥0 := {u : ℝ≥0 | s < u ∧ u ≤ t ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}
  have h0s : (0 : ℝ≥0) ≤ s := by positivity
  have hF : F.Finite := by
    simpa only [F] using
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n)
  have hS : S.Finite := hF.subset (by
    intro u hu
    exact ⟨lt_of_le_of_lt h0s hu.1, le_trans hu.2.1 htT, hu.2.2⟩)
  have hMem (u : ℝ≥0) : u ∈ S ↔ u ∈ F ∧ s < u ∧ u ≤ t := by
    constructor
    · rintro ⟨hus, hut, hband⟩
      exact ⟨⟨lt_of_le_of_lt h0s hus, le_trans hut htT, hband⟩, hus, hut⟩
    · rintro ⟨⟨_, _, hband⟩, hus, hut⟩
      exact ⟨hus, hut, hband⟩
  have hFilter : hS.toFinset = hF.toFinset.filter (fun u => s < u ∧ u ≤ t) := by
    ext u
    simpa only [Set.Finite.mem_toFinset, Finset.mem_filter] using hMem u
  calc
    _ = (S.ncard : ℝ≥0∞) := by
      simpa only [S] using
        (avram_p2_e_compensator_original_interval_negative_band_count_ncard
          X ω s t hst n)
    _ = (hS.toFinset.card : ℝ≥0∞) := by
      rw [Set.ncard_eq_toFinset_card S hS]
    _ = (hF.toFinset.filter (fun u => s < u ∧ u ≤ t)).card := by
      rw [hFilter]
