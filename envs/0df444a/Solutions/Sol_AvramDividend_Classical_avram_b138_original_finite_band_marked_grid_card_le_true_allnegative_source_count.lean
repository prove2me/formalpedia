-- Prove2me | solution 1 for AvramDividend.Classical.avram_b138_original_finite_band_marked_grid_card_le_true_allnegative_source_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:41:12.767307+00:00
-- url     : https://prove2.me/submissions/7bcfa406-6a5f-4f48-b0be-e43c91bc04ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_count_to_finset_card
import Theorems.Thm_AvramDividend_Classical_avram_b95_original_monotone_grid_marked_cell_count_le_source_jumps
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine finite negative-band occupied source cells are dominated by the full original physical negative Poisson count. -/
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
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  have hCard : J.card ≤ F.card :=
    avram_b95_original_monotone_grid_marked_cell_count_le_source_jumps
      grid hmono J F hJ
  have hEq :=
    avram_p2_e_compensator_original_negative_band_count_to_finset_card
      X ω T n
  have hBand :
      Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))) ⊆
        Ioc 0 T ×ˢ Iio (0 : ℝ) := by
    intro z hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨hz.1, ?_⟩
    change z.2 < (0 : ℝ)
    exact lt_of_le_of_lt hz.2 (neg_lt_zero.mpr hp)
  calc
    (J.card : ℝ≥0∞) ≤ (F.card : ℝ≥0∞) := by
      exact_mod_cast hCard
    _ = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) := hEq.symm
    _ ≤ _ := measure_mono hBand
