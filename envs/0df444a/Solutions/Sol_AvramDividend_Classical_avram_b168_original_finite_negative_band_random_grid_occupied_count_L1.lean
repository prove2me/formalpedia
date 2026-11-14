-- Prove2me | solution 1 for AvramDividend.Classical.avram_b168_original_finite_negative_band_random_grid_occupied_count_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:54:58.630874+00:00
-- url     : https://prove2.me/submissions/a8ef9f8b-5f23-4c35-8aa8-fa1af7504246

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The number of actual original negative finite-band jump containing cells of any bounded random monotone stopped grid is integrable under finite negative source activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n cut : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hJ : ∀ᵐ ω ∂P, ∀ i ∈ J ω,
      ∃ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T cut).toFinset,
        u ∈ Ioc (grid ω i) (grid ω (i + 1))) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by
  have hDom : ∀ᵐ ω ∂P, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by
    filter_upwards [hJ] with ω hω
    exact avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
      X ω T cut (grid ω) (hMono ω) (J ω) hω
  have hSource :=
    avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
      X hFinite n (fun _ : Ω => T) (by intro _; exact hT)
  exact lt_of_le_of_lt (lintegral_mono_ae hDom) hSource
