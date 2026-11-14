-- Prove2me | solution 1 for AvramDividend.Classical.avram_b200_original_true_marked_grid_real_count_dom_poisson_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:44:28.116907+00:00
-- url     : https://prove2.me/submissions/95787c1f-1912-4473-ad7c-cf1f60c55768

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original physical marked monotone stopped-grid cardinal is dominated in the reals by the genuine full negative Poisson source count almost everywhere under finite negative activity. -/
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
    ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by
  have hCountMeas :=
    avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
      X (fun _ : Ω => T) measurable_const
  have hFiniteCount :=
    avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
      X hFinite n (fun _ : Ω => T) (fun _ => hT)
      hCountMeas.aemeasurable
  filter_upwards [hMarks, hRange, hFiniteCount] with ω hm hr hcount
  have hLE :=
    avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
      X ω T (grid ω) (hMono ω) (J ω) hm hr
  have hReal := ENNReal.toReal_mono (ne_of_lt hcount) hLE
  simpa only [ENNReal.toReal_natCast] using hReal
