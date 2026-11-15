-- Prove2me | solution 2 for AvramDividend.Classical.avram_b138_original_finite_band_marked_grid_card_le_true_allnegative_source_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:42:31.209016+00:00
-- url     : https://prove2.me/submissions/6d36bdf8-892f-4c84-99c5-42e10c44eefc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (J : Finset ℕ)
    (hJ : ∀ i ∈ J,
      ∃ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset,
        u ∈ Ioc (grid i) (grid (i + 1))) :
    (J.card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by
  exact avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
    X ω T n grid hmono J hJ
