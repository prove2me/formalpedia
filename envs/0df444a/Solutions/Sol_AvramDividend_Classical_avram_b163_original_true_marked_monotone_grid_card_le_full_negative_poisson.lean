-- Prove2me | solution 1 for AvramDividend.Classical.avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:54:22.478309+00:00
-- url     : https://prove2.me/submissions/aab0bf7f-2bab-4ee3-ae64-34c3e33e0a0f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All genuine jump-containing cells of a finite monotone original source grid before a bounded physical horizon are dominated by the full same-source negative Poisson count, without any chosen cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0)
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (J : Finset ℕ)
    (hJ : ∀ i ∈ J, ∃ u : ℝ≥0,
      grid i < u ∧ u ≤ grid (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRange : ∀ i ∈ J, grid (i + 1) ≤ T) :
    (J.card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by
  obtain ⟨N, hN⟩ :=
    avram_b118_original_finite_physically_marked_cells_one_cutoff
      X ω J grid (fun i => grid (i + 1)) hJ
  have hSelected : ∀ i ∈ J,
      ∃ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T N).toFinset, u ∈ Ioc (grid i) (grid (i + 1)) := by
    intro i hi
    obtain ⟨u, hsu, hut, hband⟩ := hN i hi
    have hu : 0 < u := lt_of_le_of_lt zero_le hsu
    have hT : u ≤ T := hut.trans (hRange i hi)
    refine ⟨u, ?_, ⟨hsu, hut⟩⟩
    exact (avram_wave7_06_original_negative_band_marked_times_finite
      X ω T N).mem_toFinset.mpr ⟨hu, hT, hband⟩
  exact avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
    X ω T N grid hmono J hSelected
