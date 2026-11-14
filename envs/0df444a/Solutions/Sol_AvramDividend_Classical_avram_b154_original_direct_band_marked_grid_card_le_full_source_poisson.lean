-- Prove2me | solution 1 for AvramDividend.Classical.avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:49:17.637326+00:00
-- url     : https://prove2.me/submissions/3c4caa61-4faf-45e5-ad40-3debb62bc310

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_count_to_finset_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique
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
  have hCard : J.card ≤ F.card := by
    classical
    let g : ℕ → ℝ≥0 := fun i =>
      if hi : i ∈ J then Classical.choose (hJ i hi) else 0
    have hG (i : ℕ) (hi : i ∈ J) :
        g i ∈ F ∧ g i ∈ Ioc (grid i) (grid (i + 1)) := by
      simpa only [g, dif_pos hi] using Classical.choose_spec (hJ i hi)
    have hMap : Set.MapsTo g (J : Set ℕ) (F : Set ℝ≥0) := by
      intro i hi
      exact (hG i hi).1
    have hInj : Set.InjOn g (J : Set ℕ) := by
      intro i hi j hj heq
      have hLeft := (hG i hi).2
      have hRight : g i ∈ Ioc (grid j) (grid (j + 1)) := by
        simpa only [heq] using (hG j hj).2
      exact avram_wave7_06_monotone_marked_grid_index_unique
        grid hmono (g i) i j hLeft hRight
    exact Finset.card_le_card_of_injOn g hMap hInj
  have hEq :=
    avram_p2_e_compensator_original_negative_band_count_to_finset_card
      X ω T n
  have hBand :
      Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))) ⊆
        Ioc 0 T ×ˢ Iio (0 : ℝ) := by
    intro z hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨hz.1, lt_of_le_of_lt hz.2 (neg_lt_zero.mpr hp)⟩
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
