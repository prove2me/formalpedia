-- Prove2me | solution 1 for AvramDividend.Classical.avram_b202_original_finite_band_marked_grid_real_poisson_dom_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:49:09.207622+00:00
-- url     : https://prove2.me/submissions/522a1c36-37bc-4a43-bc3e-a51e28a2a112

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original bounded finite-negative-band marked random grid contact count is dominated almost everywhere by the real full-negative Poisson source count. -/
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
  filter_upwards [hJ, hFiniteCount] with ω hω hcount
  have hLE :=
    avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
      X ω T cut (grid ω) (hMono ω) (J ω) hω
  have hReal := ENNReal.toReal_mono (ne_of_lt hcount) hLE
  simpa only [ENNReal.toReal_natCast] using hReal
