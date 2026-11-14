-- Prove2me | solution 1 for AvramDividend.Classical.avram_b165_original_true_bounded_random_monotone_marked_grid_count_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:58:52.509081+00:00
-- url     : https://prove2.me/submissions/e02d0bd7-ed2f-40dc-9b88-f2ad0c0ef02d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual number of original physical negative-jump containing cells of any bounded random monotone stopped grid has finite source expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hMarks : ∀ᵐ ω ∂P, ∀ i ∈ J ω, ∃ u : ℝ≥0,
      grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRange : ∀ᵐ ω ∂P, ∀ i ∈ J ω, grid ω (i + 1) ≤ T) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by
  have hDom : ∀ᵐ ω ∂P, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by
    filter_upwards [hMarks, hRange] with ω hm hr
    exact avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
      X ω T (grid ω) (hMono ω) (J ω) hm hr
  have hSource :=
    avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
      X hFinite n (fun _ : Ω => T) (by intro _; exact hT)
  exact lt_of_le_of_lt (lintegral_mono_ae hDom) hSource
